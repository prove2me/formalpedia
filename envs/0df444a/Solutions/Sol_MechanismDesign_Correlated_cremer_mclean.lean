-- Prove2me | solution 1 for MechanismDesign.Correlated.cremer_mclean
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:03:09.31399+00:00
-- url     : https://prove2.me/submissions/fc3f1e15-8847-4738-a7aa-46e036971442

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel



namespace MechanismDesign.Correlated

open FiniteTypes

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]

lemma cm_sum_fib (i : ι) (x y : Θ i) (G : (∀ j, Θ j) → ℝ)
    (hG : ∀ θ a, G (Function.update θ i a) = G θ) :
    ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), G θ =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y), G θ := by
  apply Finset.sum_nbij' (fun θ => Function.update θ i y) (fun θ => Function.update θ i x)
  · intro θ _; simp
  · intro θ _; simp
  · intro θ hθ
    have hθ' : θ i = x := by simpa using hθ
    simp only [Function.update_idem]
    rw [← hθ']; exact Function.update_eq_self i θ
  · intro θ hθ
    have hθ' : θ i = y := by simpa using hθ
    simp only [Function.update_idem]
    rw [← hθ']; exact Function.update_eq_self i θ
  · intro θ _; rw [hG]

lemma cm_condProb_inv (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (θ : ∀ j, Θ j) (a : Θ i) :
    condProb μ i x (Function.update θ i a) = condProb μ i x θ := by
  simp [condProb]

lemma cm_condExp_congr (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (g g' : (∀ j, Θ j) → ℝ)
    (h : ∀ θ, θ i = x → g θ = g' θ) : condExp μ i x g = condExp μ i x g' := by
  unfold condExp
  apply Finset.sum_congr rfl
  intro θ hθ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  rw [h θ hθ]

lemma cm_condExp_lin (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (a b : (∀ j, Θ j) → ℝ) (c : ℝ) :
    condExp μ i x (fun θ => a θ - c * b θ) = condExp μ i x a - c * condExp μ i x b := by
  unfold condExp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro θ _; ring

lemma cm_condExp_inv (μ : (∀ i, Θ i) → ℝ) (i : ι) (x y : Θ i) (G : (∀ j, Θ j) → ℝ)
    (hG : ∀ θ a, G (Function.update θ i a) = G θ) :
    condExp μ i x G =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y), G θ * condProb μ i x θ := by
  unfold condExp
  apply cm_sum_fib
  intro θ a
  rw [hG, cm_condProb_inv]

lemma cm_condExp_one (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (i : ι) (x : Θ i) :
    condExp μ i x (fun _ => 1) = 1 := by
  obtain ⟨θs, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
    (by rw [hμ.2]; norm_num)
  have hpos : 0 < typeProb μ i x := by
    unfold typeProb
    exact Finset.sum_pos' (fun θ _ => (hμ.1 θ).le)
      ⟨Function.update θs i x, by simp, hμ.1 _⟩
  unfold condExp condProb
  have : ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x),
      (1 : ℝ) * (μ (Function.update θ i x) / typeProb μ i x) =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), μ θ / typeProb μ i x := by
    apply Finset.sum_congr rfl
    intro θ hθ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
    rw [← hθ, Function.update_eq_self, one_mul]
  rw [this, ← Finset.sum_div]
  exact div_self hpos.ne'

lemma cm_score (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (i : ι) (y : Θ i) :
    ∃ d : (∀ j, Θ j) → ℝ, (∀ θ a, d (Function.update θ i a) = d θ) ∧
      condExp μ i y d = 0 ∧ ∀ x, x ≠ y → 0 < condExp μ i x d := by
  classical
  let P : Θ i → ((∀ j, Θ j) → ℝ) := fun x θ => if θ i = y then condProb μ i x θ else 0
  let L : (Θ i → ℝ) →ₗ[ℝ] ((∀ j, Θ j) → ℝ) :=
    { toFun := fun w => ∑ x ∈ Finset.univ.erase y, w x • P x
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul] }
  have hconv : Convex ℝ (L '' stdSimplex ℝ (Θ i)) := (convex_stdSimplex ℝ _).linear_image L
  have hclosed : IsClosed (L '' stdSimplex ℝ (Θ i)) :=
    ((isCompact_stdSimplex ℝ _).image L.continuous_of_finiteDimensional).isClosed
  have hdisj : P y ∉ L '' stdSimplex ℝ (Θ i) := by
    rintro ⟨w, hw, hLw⟩
    apply hCM
    refine ⟨i, y, w, fun x _ => hw.1 x, fun θ => ?_⟩
    have := congrFun hLw (Function.update θ i y)
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, P, Function.update_self, if_true, cm_condProb_inv] at this
    exact this.symm
  obtain ⟨f, u0, hfu, hb⟩ := geometric_hahn_banach_point_closed hconv hclosed hdisj
  have hLx : ∀ x, x ≠ y → L (Pi.single x 1) = P x := by
    intro x hx
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩) h
  have hsingle : ∀ x : Θ i, (Pi.single x (1:ℝ)) ∈ stdSimplex ℝ (Θ i) := by
    intro x
    refine ⟨fun z => ?_, ?_⟩
    · simp only [Pi.single_apply]; split_ifs <;> norm_num
    · simp
  have hgap : ∀ x, x ≠ y → f (P y) < f (P x) := by
    intro x hx
    have := hb _ ⟨_, hsingle x, hLx x hx⟩
    linarith
  let φ : (∀ j, Θ j) → ℝ := fun θ => f (fun j => if θ = j then 1 else 0)
  have hf : ∀ v : (∀ j, Θ j) → ℝ, f v = ∑ θ, v θ * φ θ := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro θ _
    rw [map_smul, smul_eq_mul]
  have hfP : ∀ x, f (P x) = ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y),
      φ θ * condProb μ i x θ := by
    intro x
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro θ _
    simp only [P]
    split_ifs <;> ring
  have hone : ∀ x, ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y),
      condProb μ i x θ = 1 := by
    intro x
    rw [← cm_condExp_one μ hμ i x, cm_condExp_inv μ i x y (fun _ => 1) (fun _ _ => rfl)]
    simp
  have hval : ∀ x, condExp μ i x (fun θ => φ (Function.update θ i y) - f (P y)) =
      f (P x) - f (P y) := by
    intro x
    rw [cm_condExp_inv μ i x y _ (fun θ a => by simp), hfP x]
    have : ∀ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y),
        (φ (Function.update θ i y) - f (P y)) * condProb μ i x θ =
        φ θ * condProb μ i x θ - f (P y) * condProb μ i x θ := by
      intro θ hθ
      have hθ' : θ i = y := by simpa using hθ
      rw [← hθ', Function.update_eq_self]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, hone]
    ring
  refine ⟨fun θ => φ (Function.update θ i y) - f (P y), ?_, ?_, ?_⟩
  · intro θ a; simp
  · rw [hval]; ring
  · intro x hx; rw [hval]; linarith [hgap x hx]

end

theorem cremer_mclean_core {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' := by
  choose d hdinv hd0 hdpos using fun i y => cm_score μ hμ hCM i y
  let B : ∀ i, Θ i → Θ i → ℝ := fun i x y =>
    condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x - M.t i (Function.update θ i y)) -
      condExp μ i x (fun θ => u i (M.q θ) x - M.t i θ)
  let K : ι → ℝ := fun i => ∑ x, ∑ y, |B i x y| / |condExp μ i x (d i y)|
  refine ⟨⟨M.q, fun i θ => M.t i θ + K i * d i (θ i) θ⟩, rfl, ?_, ?_⟩
  · intro i x
    have : condExp μ i x (fun θ => M.t i θ + K i * d i (θ i) θ) =
        condExp μ i x (fun θ => M.t i θ - (-K i) * d i x θ) := by
      apply cm_condExp_congr; intro θ hθ; rw [hθ]; ring
    show _ = condExp μ i x (fun θ => M.t i θ + K i * d i (θ i) θ)
    rw [this, cm_condExp_lin, hd0]; ring
  · intro i x y
    show condExp μ i x (fun θ => u i (M.q θ) x - (M.t i θ + K i * d i (θ i) θ)) ≥
      condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x -
        (M.t i (Function.update θ i y) + K i * d i ((Function.update θ i y) i)
          (Function.update θ i y)))
    have h1 : condExp μ i x (fun θ => u i (M.q θ) x - (M.t i θ + K i * d i (θ i) θ)) =
        condExp μ i x (fun θ => (u i (M.q θ) x - M.t i θ) - K i * d i x θ) := by
      apply cm_condExp_congr; intro θ hθ; rw [hθ]; ring
    have h2 : condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x -
        (M.t i (Function.update θ i y) + K i * d i ((Function.update θ i y) i)
          (Function.update θ i y))) =
        condExp μ i x (fun θ => (u i (M.q (Function.update θ i y)) x -
          M.t i (Function.update θ i y)) - K i * d i y θ) := by
      apply cm_condExp_congr; intro θ _; rw [Function.update_self, hdinv]; ring
    rw [h1, h2, cm_condExp_lin, cm_condExp_lin, hd0]
    by_cases hxy : x = y
    · subst hxy
      have : condExp μ i x (fun θ => u i (M.q (Function.update θ i x)) x -
          M.t i (Function.update θ i x)) = condExp μ i x (fun θ => u i (M.q θ) x - M.t i θ) := by
        apply cm_condExp_congr; intro θ hθ; rw [← hθ, Function.update_eq_self]
      rw [this, hd0]
    · have hg := hdpos i y x hxy
      have hK : |B i x y| / |condExp μ i x (d i y)| ≤ K i := by
        have h3 : |B i x y| / |condExp μ i x (d i y)| ≤ ∑ y', |B i x y'| / |condExp μ i x (d i y')| :=
          Finset.single_le_sum (f := fun y' => |B i x y'| / |condExp μ i x (d i y')|)
            (fun _ _ => by positivity) (Finset.mem_univ y)
        have h4 : ∑ y', |B i x y'| / |condExp μ i x (d i y')| ≤ K i :=
          Finset.single_le_sum (f := fun x' => ∑ y', |B i x' y'| / |condExp μ i x' (d i y')|)
            (fun _ _ => by positivity) (Finset.mem_univ x)
        linarith
      rw [abs_of_pos hg, div_le_iff₀ hg] at hK
      have := le_abs_self (B i x y)
      simp only [B] at this hK
      linarith

end MechanismDesign.Correlated

open MechanismDesign.Correlated
open FiniteTypes

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' := by
  exact cremer_mclean_core μ hμ hCM u M
