-- Prove2me | solution 1 for Hairer.multiplication
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T19:20:04.773192+00:00
-- url     : https://prove2.me/submissions/9f1aeb66-cc95-4e82-88d9-af113f980ef4

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

variable {A : Set ℝ} {E : A → Type}
  [∀ a : A, NormedAddCommGroup (E a)] [∀ a : A, NormedSpace ℝ (E a)]

private lemma snorm_nonneg {d : ℕ} (s : Fin d → ℕ) (x : Pt d) :
    0 ≤ snorm s x := by
  cases d with
  | zero => simp [snorm]
  | succ d =>
      unfold snorm
      have hterm : 0 ≤ |x 0| ^ ((1 : ℝ) / (s 0 : ℝ)) :=
        Real.rpow_nonneg (abs_nonneg _) _
      exact hterm.trans (le_ciSup
        (f := fun i : Fin (d + 1) => |x i| ^ ((1 : ℝ) / (s i : ℝ)))
        (Finite.bddAbove_range _) (0 : Fin (d + 1)))

private def degreesLE
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one) (r : ℝ) :
    Finset A :=
  (hT.locallyFinite r).toFinset.attach.map
    { toFun := fun a => (⟨a.1, by
          have ha : a.1 ∈ A ∧ a.1 ≤ r :=
            (hT.locallyFinite r).mem_toFinset.mp a.2
          exact ha.1⟩ : A)
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : A => (z : ℝ)) hab }

@[simp] private lemma mem_degreesLE
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one) (r : ℝ)
    (a : A) :
    a ∈ degreesLE hT r ↔ (a : ℝ) ≤ r := by
  constructor
  · intro ha
    rw [degreesLE, Finset.mem_map] at ha
    rcases ha with ⟨b, hb, hba⟩
    have hb' : (b.1 : ℝ) ∈ A ∧ (b.1 : ℝ) ≤ r :=
      (hT.locallyFinite r).mem_toFinset.mp b.2
    have hval : (b.1 : ℝ) = (a : ℝ) :=
      congrArg (fun z : A => (z : ℝ)) hba
    simpa [hval] using hb'.2
  · intro ha
    let b : (hT.locallyFinite r).toFinset :=
      ⟨(a : ℝ), (hT.locallyFinite r).mem_toFinset.mpr ⟨a.property, ha⟩⟩
    rw [degreesLE, Finset.mem_map]
    refine ⟨b, by simp, ?_⟩
    apply Subtype.ext
    rfl

private def degreesLT
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one) (r : ℝ) :
    Finset A :=
  (degreesLE hT r).filter fun a => (a : ℝ) < r

@[simp] private lemma mem_degreesLT
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one) (r : ℝ)
    (a : A) :
    a ∈ degreesLT hT r ↔ (a : ℝ) < r := by
  simp only [degreesLT, Finset.mem_filter, mem_degreesLE]
  exact and_iff_right_of_imp le_of_lt

private lemma support_subset_degreesLT
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) (x : Pt d) :
    (f x).support ⊆ degreesLT hT γ := by
  intro a ha
  rw [mem_degreesLT]
  by_contra hnot
  have hz := hf.vanishing x a (le_of_not_gt hnot)
  exact (DFinsupp.mem_support_iff.mp ha) hz

private lemma eq_sum_incl_proj (τ : ModelSpace A E) :
    τ = ∑ a ∈ τ.support, incl a (proj a τ) := by
  change τ = ∑ a ∈ τ.support, DFinsupp.single a (τ a)
  simpa only [DFinsupp.sum] using
    (DFinsupp.sum_single (f := τ)).symm

private lemma proj_gam_incl_eq_zero_of_lt
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E} (hΓ : Γ ∈ G)
    (a b : A) (τ : E a) (hab : (a : ℝ) < (b : ℝ)) :
    proj b (Γ (incl a τ)) = 0 := by
  have ht := hT.triangular Γ hΓ a b τ hab.le
  rw [map_sub] at ht
  have hi : proj b (incl a τ) = 0 := by
    rw [DirectSum.component.of]
    split
    · rename_i h
      exact absurd (congrArg (fun z : A => (z : ℝ)) h) hab.ne
    · rfl
  simpa [hi] using ht

private lemma proj_gam_incl_eq_self
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E} (hΓ : Γ ∈ G)
    (a : A) (τ : E a) : proj a (Γ (incl a τ)) = τ := by
  have ht := hT.triangular Γ hΓ a a τ le_rfl
  rw [map_sub] at ht
  have hi : proj a (incl a τ) = τ := by simp [DirectSum.component.of]
  simpa [hi] using sub_eq_zero.mp ht

private lemma support_gam_incl_subset_degreesLE
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E} (hΓ : Γ ∈ G)
    (a : A) (τ : E a) :
    (Γ (incl a τ)).support ⊆ degreesLE hT (a : ℝ) := by
  intro b hb
  rw [mem_degreesLE]
  by_contra hnot
  exact (DFinsupp.mem_support_iff.mp hb)
    (proj_gam_incl_eq_zero_of_lt hT hΓ a b τ (lt_of_not_ge hnot))

private lemma gam_vanishing
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ} {r : ℕ}
    {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (x y : Pt d) (b : A) (hb : γ ≤ (b : ℝ)) :
    proj b (Gam x y (f y)) = 0 := by
  rw [eq_sum_incl_proj (f y), map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have haγ : (a : ℝ) < γ := by
    by_contra hnot
    have hz := hf.vanishing y a (le_of_not_gt hnot)
    exact (DFinsupp.mem_support_iff.mp ha) hz
  exact proj_gam_incl_eq_zero_of_lt hT (hmod.gam_mem x y) a b _ (haγ.trans_le hb)

private def fixedTruncProd
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} (γ γ₁ γ₂ : ℝ)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (f g : Pt d → ModelSpace A E) (x : Pt d) : ModelSpace A E :=
  ∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
    if (m : ℝ) + (n : ℝ) < γ then
      star (incl m (proj m (f x))) (incl n (proj n (g x)))
    else 0

private def fixedBilin
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    (γ₁ γ₂ : ℝ)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (u v : ModelSpace A E) : ModelSpace A E :=
  ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
    star (incl a (proj a u)) (incl b (proj b v))

private def fixedBilinLE
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    (a b : A)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (u v : ModelSpace A E) : ModelSpace A E :=
  ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
    star (incl p (proj p u)) (incl q (proj q v))

private def sourceBilin
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    (γ₁ γ₂ : ℝ)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)
    (u v : ModelSpace A E) : ModelSpace A E :=
  ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
    star (Γ (incl a (proj a u))) (Γ (incl b (proj b v)))

private def sourceBilinLow
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    (γ γ₁ γ₂ : ℝ)
    (star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E)
    (Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)
    (u v : ModelSpace A E) : ModelSpace A E :=
  ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
    if (a : ℝ) + (b : ℝ) < γ then
      star (Γ (incl a (proj a u))) (Γ (incl b (proj b v)))
    else 0

private lemma support_subset_degreesLT_of_vanishing
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ : ℝ} {u : ModelSpace A E}
    (hu : ∀ b : A, γ ≤ (b : ℝ) → proj b u = 0) :
    u.support ⊆ degreesLT hT γ := by
  intro b hb
  rw [mem_degreesLT]
  by_contra hnot
  exact (DFinsupp.mem_support_iff.mp hb) (hu b (le_of_not_gt hnot))

private lemma star_eq_fixedBilin
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ₁ γ₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    {u v : ModelSpace A E}
    (hu : ∀ b : A, γ₁ ≤ (b : ℝ) → proj b u = 0)
    (hv : ∀ b : A, γ₂ ≤ (b : ℝ) → proj b v = 0) :
    star u v = fixedBilin hT γ₁ γ₂ star u v := by
  calc
    star u v = star (∑ a ∈ u.support, incl a (proj a u)) v :=
      congrArg (fun z => star z v) (eq_sum_incl_proj u)
    _ = ∑ a ∈ u.support, star (incl a (proj a u)) v := by
      simp only [map_sum, LinearMap.sum_apply]
    _ =
        ∑ a ∈ u.support, ∑ b ∈ v.support,
          star (incl a (proj a u)) (incl b (proj b v)) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        star (incl a (proj a u)) v =
            star (incl a (proj a u))
              (∑ b ∈ v.support, incl b (proj b v)) :=
          congrArg (star (incl a (proj a u))) (eq_sum_incl_proj v)
        _ = ∑ b ∈ v.support,
            star (incl a (proj a u)) (incl b (proj b v)) := by
          simp only [map_sum]
    _ = ∑ a ∈ u.support, ∑ b ∈ degreesLT hT γ₂,
          star (incl a (proj a u)) (incl b (proj b v)) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_subset (support_subset_degreesLT_of_vanishing hT hv)
      intro b hb hbs
      have hb0 : proj b v = 0 := DFinsupp.notMem_support_iff.mp hbs
      simp [hb0]
    _ = fixedBilin hT γ₁ γ₂ star u v := by
      unfold fixedBilin
      apply Finset.sum_subset (support_subset_degreesLT_of_vanishing hT hu)
      intro a ha has
      have ha0 : proj a u = 0 := DFinsupp.notMem_support_iff.mp has
      simp [ha0]

private lemma star_eq_fixedBilinLE
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    (a b : A)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    {u v : ModelSpace A E}
    (hu : u.support ⊆ degreesLE hT (a : ℝ))
    (hv : v.support ⊆ degreesLE hT (b : ℝ)) :
    star u v = fixedBilinLE hT a b star u v := by
  calc
    star u v = star (∑ p ∈ u.support, incl p (proj p u)) v :=
      congrArg (fun z => star z v) (eq_sum_incl_proj u)
    _ = ∑ p ∈ u.support, star (incl p (proj p u)) v := by
      simp only [map_sum, LinearMap.sum_apply]
    _ = ∑ p ∈ u.support, ∑ q ∈ v.support,
        star (incl p (proj p u)) (incl q (proj q v)) := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        star (incl p (proj p u)) v =
            star (incl p (proj p u)) (∑ q ∈ v.support, incl q (proj q v)) :=
          congrArg (star (incl p (proj p u))) (eq_sum_incl_proj v)
        _ = ∑ q ∈ v.support,
            star (incl p (proj p u)) (incl q (proj q v)) := by
          simp only [map_sum]
    _ = ∑ p ∈ u.support, ∑ q ∈ degreesLE hT (b : ℝ),
        star (incl p (proj p u)) (incl q (proj q v)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_subset hv
      intro q hq hqs
      have hq0 : proj q v = 0 := DFinsupp.notMem_support_iff.mp hqs
      simp [hq0]
    _ = fixedBilinLE hT a b star u v := by
      unfold fixedBilinLE
      apply Finset.sum_subset hu
      intro p hp hps
      have hp0 : proj p u = 0 := DFinsupp.notMem_support_iff.mp hps
      simp [hp0]

private lemma star_gam_eq_sourceBilin
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ₁ γ₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) {u v : ModelSpace A E}
    (hu : ∀ b : A, γ₁ ≤ (b : ℝ) → proj b u = 0)
    (hv : ∀ b : A, γ₂ ≤ (b : ℝ) → proj b v = 0) :
    star (Γ u) (Γ v) = sourceBilin hT γ₁ γ₂ star Γ u v := by
  have hΓu : Γ u = ∑ a ∈ degreesLT hT γ₁, Γ (incl a (proj a u)) := by
    calc
      Γ u = Γ (∑ a ∈ u.support, incl a (proj a u)) :=
        congrArg Γ (eq_sum_incl_proj u)
      _ = ∑ a ∈ u.support, Γ (incl a (proj a u)) := by simp only [map_sum]
      _ = ∑ a ∈ degreesLT hT γ₁, Γ (incl a (proj a u)) := by
        apply Finset.sum_subset (support_subset_degreesLT_of_vanishing hT hu)
        intro a ha has
        have ha0 : proj a u = 0 := DFinsupp.notMem_support_iff.mp has
        simp [ha0]
  have hΓv : Γ v = ∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v)) := by
    calc
      Γ v = Γ (∑ b ∈ v.support, incl b (proj b v)) :=
        congrArg Γ (eq_sum_incl_proj v)
      _ = ∑ b ∈ v.support, Γ (incl b (proj b v)) := by simp only [map_sum]
      _ = ∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v)) := by
        apply Finset.sum_subset (support_subset_degreesLT_of_vanishing hT hv)
        intro b hb hbs
        have hb0 : proj b v = 0 := DFinsupp.notMem_support_iff.mp hbs
        simp [hb0]
  rw [hΓu, hΓv]
  unfold sourceBilin
  calc
    star (∑ a ∈ degreesLT hT γ₁, Γ (incl a (proj a u)))
        (∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v))) =
      (∑ a ∈ degreesLT hT γ₁, star (Γ (incl a (proj a u))))
        (∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v))) := by
      exact congrArg
        (fun L : ModelSpace A E →ₗ[ℝ] ModelSpace A E =>
          L (∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v))))
        (map_sum star (fun a => Γ (incl a (proj a u))) (degreesLT hT γ₁))
    _ =
      ∑ a ∈ degreesLT hT γ₁,
        star (Γ (incl a (proj a u)))
          (∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v))) := by
      exact LinearMap.sum_apply (degreesLT hT γ₁)
        (fun a => star (Γ (incl a (proj a u))))
        (∑ b ∈ degreesLT hT γ₂, Γ (incl b (proj b v)))
    _ = ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        star (Γ (incl a (proj a u))) (Γ (incl b (proj b v))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact map_sum (star (Γ (incl a (proj a u))))
        (fun b => Γ (incl b (proj b v))) (degreesLT hT γ₂)

private lemma truncProd_component_eq_full
    {d : ℕ} {γ : ℝ}
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (f g : Pt d → ModelSpace A E)
    (x : Pt d) (c : A) (hc : (c : ℝ) < γ) :
    proj c (truncProd γ star f g x) = proj c (star (f x) (g x)) := by
  simp only [truncProd, map_sum]
  have hfull :
      proj c (star (f x) (g x)) =
        ∑ a ∈ (f x).support, ∑ b ∈ (g x).support,
          proj c (star (incl a (proj a (f x))) (incl b (proj b (g x)))) := by
    calc
      proj c (star (f x) (g x)) =
          proj c (star (∑ a ∈ (f x).support, incl a (proj a (f x))) (g x)) :=
        congrArg (fun z => proj c (star z (g x))) (eq_sum_incl_proj (f x))
      _ = ∑ a ∈ (f x).support,
          proj c (star (incl a (proj a (f x))) (g x)) := by
        simp only [map_sum, LinearMap.sum_apply]
      _ = ∑ a ∈ (f x).support, ∑ b ∈ (g x).support,
          proj c (star (incl a (proj a (f x))) (incl b (proj b (g x)))) := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          proj c (star (incl a (proj a (f x))) (g x)) =
              proj c (star (incl a (proj a (f x)))
                (∑ b ∈ (g x).support, incl b (proj b (g x)))) :=
            congrArg (fun z => proj c (star (incl a (proj a (f x))) z))
              (eq_sum_incl_proj (g x))
          _ = ∑ b ∈ (g x).support,
              proj c (star (incl a (proj a (f x))) (incl b (proj b (g x)))) := by
            simp only [map_sum]
  rw [hfull]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs with hab
  · rfl
  · symm
    exact hstar.graded a b c _ _ (by
      intro heq
      exact hab (heq ▸ hc))

private lemma truncProd_eq_fixedTruncProd
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ} {γ γ₁ γ₂ : ℝ}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    {f g : Pt d → ModelSpace A E}
    (hf : IsModelled s γ₁ Gam f) (hg : IsModelled s γ₂ Gam g) (x : Pt d) :
    truncProd γ star f g x = fixedTruncProd hT γ γ₁ γ₂ star f g x := by
  unfold truncProd fixedTruncProd
  calc
    (∑ m ∈ (f x).support, ∑ n ∈ (g x).support,
        if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0) =
      ∑ m ∈ (f x).support, ∑ n ∈ degreesLT hT γ₂,
        if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_subset (support_subset_degreesLT hT hg x)
      intro n hn hns
      have hn0 : proj n (g x) = 0 := DFinsupp.notMem_support_iff.mp hns
      simp [hn0]
    _ = ∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
        if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0 := by
      apply Finset.sum_subset (support_subset_degreesLT hT hf x)
      intro m hm hms
      have hm0 : proj m (f x) = 0 := DFinsupp.notMem_support_iff.mp hms
      simp [hm0]

private lemma gam_truncProd_eq_sourceBilinLow
    {d : ℕ} {s : Fin d → ℕ}
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    {V W : ∀ a : A, Submodule ℝ (E a)}
    {γ γ₁ γ₂ : ℝ} (hreg : IsGammaRegular G V W star γ)
    {f₁ f₂ : Pt d → ModelSpace A E}
    (hf₁ : IsModelled s γ₁ Gam f₁) (hf₁V : TakesValuesIn V f₁)
    (hf₂ : IsModelled s γ₂ Gam f₂) (hf₂W : TakesValuesIn W f₂)
    (x y : Pt d) :
    Gam x y (truncProd γ star f₁ f₂ y) =
      sourceBilinLow hT γ γ₁ γ₂ star (Gam x y) (f₁ y) (f₂ y) := by
  rw [truncProd_eq_fixedTruncProd hT hf₁ hf₂]
  unfold fixedTruncProd sourceBilinLow
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs with hab
  · exact hreg (Gam x y) (hmod.gam_mem x y) a b hab
      (proj a (f₁ y)) (hf₁V y a) (proj b (f₂ y)) (hf₂W y b)
  · simp

private noncomputable def productBound
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (a b : A) : ℝ :=
  max 0 (Classical.choose (hstar.bounded a b))

private lemma product_bound
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (a b c : A) (σ : E a) (τ : E b) :
    ‖proj c (star (incl a σ) (incl b τ))‖ ≤
      productBound hstar a b * ‖σ‖ * ‖τ‖ := by
  let C := Classical.choose (hstar.bounded a b)
  have hC := Classical.choose_spec (hstar.bounded a b) σ τ c
  calc
    ‖proj c (star (incl a σ) (incl b τ))‖ ≤ C * ‖σ‖ * ‖τ‖ := hC
    _ ≤ max 0 C * ‖σ‖ * ‖τ‖ := by
      gcongr
      exact le_max_right 0 C

private lemma productBound_nonneg
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (a b : A) :
    0 ≤ productBound hstar a b := by
  exact le_max_left _ _

private lemma IsProduct.flip
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) : IsProduct one star.flip where
  graded a b c σ τ hne :=
    hstar.graded b a c τ σ (by
      intro h
      apply hne
      linarith)
  one_left τ := hstar.one_right τ
  one_right τ := hstar.one_left τ
  bounded a b := by
    obtain ⟨C, hC⟩ := hstar.bounded b a
    exact ⟨C, fun σ τ c => by
      calc
        ‖proj c (star.flip (incl a σ) (incl b τ))‖ ≤ C * ‖τ‖ * ‖σ‖ := hC τ σ c
        _ = C * ‖σ‖ * ‖τ‖ := by ring⟩

private lemma fixedBilin_component_norm_le
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ₁ γ₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (u v : ModelSpace A E) (c : A) :
    ‖proj c (fixedBilin hT γ₁ γ₂ star u v)‖ ≤
      ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ := by
  simp only [fixedBilin, map_sum]
  calc
    ‖∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ ≤
      ∑ a ∈ degreesLT hT γ₁,
        ‖∑ b ∈ degreesLT hT γ₂,
          proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        ‖proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact product_bound hstar a b c _ _

private lemma fixedBilin_component_norm_le_graded
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ₁ γ₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (u v : ModelSpace A E) (c : A) :
    ‖proj c (fixedBilin hT γ₁ γ₂ star u v)‖ ≤
      ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        if (c : ℝ) = (a : ℝ) + (b : ℝ) then
          productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ else 0 := by
  simp only [fixedBilin, map_sum]
  calc
    ‖∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ ≤
      ∑ a ∈ degreesLT hT γ₁,
        ‖∑ b ∈ degreesLT hT γ₂,
          proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        ‖proj c (star (incl a (proj a u)) (incl b (proj b v)))‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        if (c : ℝ) = (a : ℝ) + (b : ℝ) then
          productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with hab
      · exact product_bound hstar a b c _ _
      · rw [hstar.graded a b c _ _ hab]
        simp

private lemma fixedBilinLE_component_norm_le_graded
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (a b : A) (u v : ModelSpace A E) (c : A) :
    ‖proj c (fixedBilinLE hT a b star u v)‖ ≤
      ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        if (c : ℝ) = (p : ℝ) + (q : ℝ) then
          productBound hstar p q * ‖proj p u‖ * ‖proj q v‖ else 0 := by
  simp only [fixedBilinLE, map_sum]
  calc
    ‖∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        proj c (star (incl p (proj p u)) (incl q (proj q v)))‖ ≤
      ∑ p ∈ degreesLE hT (a : ℝ),
        ‖∑ q ∈ degreesLE hT (b : ℝ),
          proj c (star (incl p (proj p u)) (incl q (proj q v)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        ‖proj c (star (incl p (proj p u)) (incl q (proj q v)))‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_sum_le _ _
    _ ≤ ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        if (c : ℝ) = (p : ℝ) + (q : ℝ) then
          productBound hstar p q * ‖proj p u‖ * ‖proj q v‖ else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hpq
      · exact product_bound hstar p q c _ _
      · rw [hstar.graded p q c _ _ hpq]
        simp

private lemma rpow_le_rpow_of_le_one {ρ p q : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hqp : q ≤ p) (hq : 0 < q) :
    ρ ^ p ≤ ρ ^ q := by
  rcases hρ0.eq_or_lt with hρ | hρ
  · subst ρ
    rw [Real.zero_rpow hq.ne', Real.zero_rpow (hq.trans_le hqp).ne']
  · exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hqp

private lemma rpow_add_of_nonneg {ρ p q : ℝ}
    (hρ : 0 ≤ ρ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ρ ^ (p + q) = ρ ^ p * ρ ^ q := by
  rcases hρ.eq_or_lt with hρ | hρ
  · subst ρ
    rcases hp.eq_or_lt with hp | hp
    · subst p
      simp
    · rcases hq.eq_or_lt with hq | hq
      · subst q
        simp
      · rw [Real.zero_rpow hp.ne', Real.zero_rpow hq.ne',
          Real.zero_rpow (add_pos hp hq).ne']
        simp
  · exact Real.rpow_add hρ p q

private lemma gam_component_bound
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    {γ₀ C : ℝ} {K : Set (Pt d)}
    (hGam : ∀ ℓ m : A, (ℓ : ℝ) < γ₀ → (m : ℝ) < (ℓ : ℝ) →
      ∀ a : E ℓ, ∀ x ∈ K, ∀ y ∈ K,
      ‖proj m (Gam x y (incl ℓ a))‖ ≤
        C * ‖a‖ * snorm s (x - y) ^ ((ℓ : ℝ) - (m : ℝ)))
    (a p : A) (σ : E a) {x y : Pt d} (hx : x ∈ K) (hy : y ∈ K)
    (ha : (a : ℝ) < γ₀) (hp : (p : ℝ) ≤ (a : ℝ))
    (hmem : Gam x y ∈ G) :
    ‖proj p (Gam x y (incl a σ))‖ ≤
      max 1 C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) := by
  rcases hp.eq_or_lt with hp | hp
  · have hap : a = p := Subtype.ext hp.symm
    subst p
    rw [proj_gam_incl_eq_self hT hmem]
    simp only [sub_self, Real.rpow_zero, mul_one]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (le_max_left 1 C) (norm_nonneg σ))
  · calc
      ‖proj p (Gam x y (incl a σ))‖ ≤
          C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) :=
        hGam a p ha hp σ x hx y hy
      _ ≤ max 1 C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) := by
        have hpow : 0 ≤ snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) :=
          Real.rpow_nonneg (snorm_nonneg s _) _
        calc
          C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) =
              C * (‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ))) := by ring
          _ ≤ max 1 C * (‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_right 1 C)
              (mul_nonneg (norm_nonneg σ) hpow)
          _ = max 1 C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) := by ring

private lemma transported_term_bound
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    {γ₀ C : ℝ} {K : Set (Pt d)}
    (hGam : ∀ ℓ m : A, (ℓ : ℝ) < γ₀ → (m : ℝ) < (ℓ : ℝ) →
      ∀ a : E ℓ, ∀ x ∈ K, ∀ y ∈ K,
      ‖proj m (Gam x y (incl ℓ a))‖ ≤
        C * ‖a‖ * snorm s (x - y) ^ ((ℓ : ℝ) - (m : ℝ)))
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    (a b : A) (σ : E a) (τ : E b) {x y : Pt d}
    (hx : x ∈ K) (hy : y ∈ K) (ha : (a : ℝ) < γ₀) (hb : (b : ℝ) < γ₀)
    (hmem : Gam x y ∈ G) (c : A) (hcab : (c : ℝ) ≤ (a : ℝ) + (b : ℝ)) :
    ‖proj c (star (Gam x y (incl a σ)) (Gam x y (incl b τ)))‖ ≤
      (∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        productBound hstar p q * max 1 C * max 1 C * ‖σ‖ * ‖τ‖) *
        snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := by
  rw [star_eq_fixedBilinLE hT a b
    (support_gam_incl_subset_degreesLE hT hmem a σ)
    (support_gam_incl_subset_degreesLE hT hmem b τ)]
  calc
    ‖proj c (fixedBilinLE hT a b star
        (Gam x y (incl a σ)) (Gam x y (incl b τ)))‖ ≤
      ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        if (c : ℝ) = (p : ℝ) + (q : ℝ) then
          productBound hstar p q * ‖proj p (Gam x y (incl a σ))‖ *
            ‖proj q (Gam x y (incl b τ))‖ else 0 :=
      fixedBilinLE_component_norm_le_graded hT hstar a b _ _ c
    _ ≤ ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        (productBound hstar p q * max 1 C * max 1 C * ‖σ‖ * ‖τ‖) *
          snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hpa : (p : ℝ) ≤ (a : ℝ) := mem_degreesLE hT (a : ℝ) p |>.mp hp
      have hqb : (q : ℝ) ≤ (b : ℝ) := mem_degreesLE hT (b : ℝ) q |>.mp hq
      have hρ0 : 0 ≤ snorm s (x - y) := snorm_nonneg s _
      split_ifs with hpq
      · have hpbound := gam_component_bound hT hGam a p σ hx hy ha hpa hmem
        have hqbound := gam_component_bound hT hGam b q τ hx hy hb hqb hmem
        have hpow := rpow_add_of_nonneg hρ0 (sub_nonneg.mpr hpa) (sub_nonneg.mpr hqb)
        have hP : 0 ≤ productBound hstar p q := productBound_nonneg hstar p q
        have hD : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left 1 C)
        have hpaPow : 0 ≤ snorm s (x - y) ^ ((a : ℝ) - (p : ℝ)) :=
          Real.rpow_nonneg hρ0 _
        have hqPow : 0 ≤ snorm s (x - y) ^ ((b : ℝ) - (q : ℝ)) :=
          Real.rpow_nonneg hρ0 _
        calc
          productBound hstar p q * ‖proj p (Gam x y (incl a σ))‖ *
              ‖proj q (Gam x y (incl b τ))‖ ≤
            productBound hstar p q *
                (max 1 C * ‖σ‖ * snorm s (x - y) ^ ((a : ℝ) - (p : ℝ))) *
              (max 1 C * ‖τ‖ * snorm s (x - y) ^ ((b : ℝ) - (q : ℝ))) := by
            gcongr
          _ = (productBound hstar p q * max 1 C * max 1 C * ‖σ‖ * ‖τ‖) *
              snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := by
            rw [show (a : ℝ) + (b : ℝ) - (c : ℝ) =
                ((a : ℝ) - (p : ℝ)) + ((b : ℝ) - (q : ℝ)) by linarith,
              hpow]
            ring
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (productBound_nonneg hstar p q) (le_trans zero_le_one (le_max_left 1 C)))
                (le_trans zero_le_one (le_max_left 1 C)))
              (norm_nonneg σ))
            (norm_nonneg τ))
          (Real.rpow_nonneg hρ0 _)
    _ = (∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        productBound hstar p q * max 1 C * max 1 C * ‖σ‖ * ‖τ‖) *
        snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := by
      simp_rw [Finset.sum_mul]

private lemma source_difference_component_eq_high_sum
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ γ₁ γ₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)
    (u v : ModelSpace A E) (c : A) :
    proj c (sourceBilin hT γ₁ γ₂ star Γ u v -
      sourceBilinLow hT γ γ₁ γ₂ star Γ u v) =
      ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        if γ ≤ (a : ℝ) + (b : ℝ) then
          proj c (star (Γ (incl a (proj a u))) (Γ (incl b (proj b v))))
        else 0 := by
  unfold sourceBilin sourceBilinLow
  simp only [map_sub, map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : (a : ℝ) + (b : ℝ) < γ
  · simp [hab, not_le.mpr hab]
  · simp [hab, le_of_not_gt hab]

private lemma truncation_correction_bound
    {d : ℕ} {s : Fin d → ℕ}
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    {V W : ∀ a : A, Submodule ℝ (E a)}
    {γ γ₁ γ₂ : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hreg : IsGammaRegular G V W star γ)
    {f₁ f₂ : Pt d → ModelSpace A E}
    (hf₁ : IsModelled s γ₁ Gam f₁) (hf₁V : TakesValuesIn V f₁)
    (hf₂ : IsModelled s γ₂ Gam f₂) (hf₂W : TakesValuesIn W f₂)
    {K : Set (Pt d)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, snorm s (x - y) ≤ 1 →
      ∀ c : A, (c : ℝ) < γ →
      ‖proj c (star (Gam x y (f₁ y)) (Gam x y (f₂ y)) -
        Gam x y (truncProd γ star f₁ f₂ y))‖ ≤
          C * snorm s (x - y) ^ (γ - (c : ℝ)) := by
  let γ₀ := max γ₁ γ₂
  have hγ₀ : 0 < γ₀ := hγ₁.trans_le (le_max_left γ₁ γ₂)
  obtain ⟨CG, hGam⟩ := hmod.gam_bound γ₀ hγ₀ K hK
  obtain ⟨C₁, hf₁val, _⟩ := hf₁.bound K hK
  obtain ⟨C₂, hf₂val, _⟩ := hf₂.bound K hK
  let D := ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
    ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
      productBound hstar p q * max 1 CG * max 1 CG * max 0 C₁ * max 0 C₂
  refine ⟨D, ?_⟩
  intro x hx y hy hρ c hc
  have hρ0 : 0 ≤ snorm s (x - y) := snorm_nonneg s _
  have hsource : star (Gam x y (f₁ y)) (Gam x y (f₂ y)) =
      sourceBilin hT γ₁ γ₂ star (Gam x y) (f₁ y) (f₂ y) :=
    star_gam_eq_sourceBilin hT (Gam x y) (hf₁.vanishing y) (hf₂.vanishing y)
  have hlow : Gam x y (truncProd γ star f₁ f₂ y) =
      sourceBilinLow hT γ γ₁ γ₂ star (Gam x y) (f₁ y) (f₂ y) :=
    gam_truncProd_eq_sourceBilinLow hT hmod hreg hf₁ hf₁V hf₂ hf₂W x y
  rw [hsource, hlow, source_difference_component_eq_high_sum]
  calc
    ‖∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        if γ ≤ (a : ℝ) + (b : ℝ) then
          proj c (star (Gam x y (incl a (proj a (f₁ y))))
            (Gam x y (incl b (proj b (f₂ y))))) else 0‖ ≤
      ∑ a ∈ degreesLT hT γ₁,
        ‖∑ b ∈ degreesLT hT γ₂,
          if γ ≤ (a : ℝ) + (b : ℝ) then
            proj c (star (Gam x y (incl a (proj a (f₁ y))))
              (Gam x y (incl b (proj b (f₂ y))))) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        ‖if γ ≤ (a : ℝ) + (b : ℝ) then
          proj c (star (Gam x y (incl a (proj a (f₁ y))))
            (Gam x y (incl b (proj b (f₂ y))))) else 0‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        (∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
          productBound hstar p q * max 1 CG * max 1 CG * max 0 C₁ * max 0 C₂) *
            snorm s (x - y) ^ (γ - (c : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have haγ₁ : (a : ℝ) < γ₁ := mem_degreesLT hT γ₁ a |>.mp ha
      have hbγ₂ : (b : ℝ) < γ₂ := mem_degreesLT hT γ₂ b |>.mp hb
      let R := ∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
        productBound hstar p q * max 1 CG * max 1 CG
      have hR : 0 ≤ R := by
        unfold R
        apply Finset.sum_nonneg
        intro p hp
        apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg
          (mul_nonneg (productBound_nonneg hstar p q)
            (le_trans zero_le_one (le_max_left 1 CG)))
          (le_trans zero_le_one (le_max_left 1 CG))
      split_ifs with hab
      · have hterm := transported_term_bound hT hGam hstar a b
          (proj a (f₁ y)) (proj b (f₂ y)) hx hy
          (haγ₁.trans_le (le_max_left γ₁ γ₂))
          (hbγ₂.trans_le (le_max_right γ₁ γ₂)) (hmod.gam_mem x y) c
          (hc.le.trans hab)
        have hpow : snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) ≤
            snorm s (x - y) ^ (γ - (c : ℝ)) :=
          rpow_le_rpow_of_le_one hρ0 hρ (by linarith) (by linarith)
        have hval₁ : ‖proj a (f₁ y)‖ ≤ max 0 C₁ :=
          (hf₁val y hy a haγ₁).trans (le_max_right 0 C₁)
        have hval₂ : ‖proj b (f₂ y)‖ ≤ max 0 C₂ :=
          (hf₂val y hy b hbγ₂).trans (le_max_right 0 C₂)
        calc
          ‖proj c (star (Gam x y (incl a (proj a (f₁ y))))
              (Gam x y (incl b (proj b (f₂ y)))))‖ ≤
            (∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
              productBound hstar p q * max 1 CG * max 1 CG *
                ‖proj a (f₁ y)‖ * ‖proj b (f₂ y)‖) *
              snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := hterm
          _ =
            R * ‖proj a (f₁ y)‖ * ‖proj b (f₂ y)‖ *
              snorm s (x - y) ^ ((a : ℝ) + (b : ℝ) - (c : ℝ)) := by
            unfold R
            simp_rw [Finset.sum_mul]
          _ ≤ R * max 0 C₁ * max 0 C₂ *
              snorm s (x - y) ^ (γ - (c : ℝ)) := by
            gcongr
          _ = (∑ p ∈ degreesLE hT (a : ℝ), ∑ q ∈ degreesLE hT (b : ℝ),
                productBound hstar p q * max 1 CG * max 1 CG * max 0 C₁ * max 0 C₂) *
              snorm s (x - y) ^ (γ - (c : ℝ)) := by
            unfold R
            simp_rw [Finset.sum_mul]
      · rw [norm_zero]
        exact mul_nonneg
          (by
            apply Finset.sum_nonneg
            intro p hp
            apply Finset.sum_nonneg
            intro q hq
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (productBound_nonneg hstar p q)
                    (le_trans zero_le_one (le_max_left 1 CG)))
                  (le_trans zero_le_one (le_max_left 1 CG)))
                (le_max_left 0 C₁))
              (le_max_left 0 C₂))
          (Real.rpow_nonneg hρ0 _)
    _ = D * snorm s (x - y) ^ (γ - (c : ℝ)) := by
      unfold D
      simp_rw [Finset.sum_mul]

private lemma first_increment_bound
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {γ γ₁ γ₂ α₂ ρ C₁ C₂ : ℝ}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star) (u v : ModelSpace A E)
    (hu0 : ∀ a : A, γ₁ ≤ (a : ℝ) → proj a u = 0)
    (hv0 : ∀ b : A, γ₂ ≤ (b : ℝ) → proj b v = 0)
    (hu : ∀ a : A, (a : ℝ) < γ₁ →
      ‖proj a u‖ ≤ C₁ * ρ ^ (γ₁ - (a : ℝ)))
    (hv : ∀ b : A, (b : ℝ) < γ₂ → ‖proj b v‖ ≤ C₂)
    (hvlow : ∀ b : A, (b : ℝ) < α₂ → proj b v = 0)
    (hγα : γ ≤ γ₁ + α₂) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (c : A) (hc : (c : ℝ) < γ) :
    ‖proj c (star u v)‖ ≤
      (∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
        productBound hstar a b * max 0 C₁ * max 0 C₂) *
        ρ ^ (γ - (c : ℝ)) := by
  rw [star_eq_fixedBilin hT hu0 hv0]
  calc
    ‖proj c (fixedBilin hT γ₁ γ₂ star u v)‖ ≤
        ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
          if (c : ℝ) = (a : ℝ) + (b : ℝ) then
            productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ else 0 :=
      fixedBilin_component_norm_le_graded hT hstar u v c
    _ ≤ ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
          (productBound hstar a b * max 0 C₁ * max 0 C₂) *
            ρ ^ (γ - (c : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with hab
      · by_cases hblow : (b : ℝ) < α₂
        · rw [hvlow b hblow, norm_zero]
          simp only [mul_zero]
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (productBound_nonneg hstar a b) (le_max_left 0 C₁))
              (le_max_left 0 C₂))
            (Real.rpow_nonneg hρ0 _)
        · have haγ : (a : ℝ) < γ₁ := mem_degreesLT hT γ₁ a |>.mp ha
          have hbγ : (b : ℝ) < γ₂ := mem_degreesLT hT γ₂ b |>.mp hb
          have hP : 0 ≤ productBound hstar a b := productBound_nonneg hstar a b
          have hq : 0 < γ - (c : ℝ) := by linarith
          have hqp : γ - (c : ℝ) ≤ γ₁ - (a : ℝ) := by
            have hbα : α₂ ≤ (b : ℝ) := le_of_not_gt hblow
            linarith
          have hp := rpow_le_rpow_of_le_one hρ0 hρ1 hqp hq
          have hu' : ‖proj a u‖ ≤ max 0 C₁ * ρ ^ (γ₁ - (a : ℝ)) :=
            (hu a haγ).trans (by
              gcongr
              exact le_max_right 0 C₁)
          have hv' : ‖proj b v‖ ≤ max 0 C₂ :=
            (hv b hbγ).trans (le_max_right 0 C₂)
          calc
            productBound hstar a b * ‖proj a u‖ * ‖proj b v‖ ≤
                productBound hstar a b *
                  (max 0 C₁ * ρ ^ (γ₁ - (a : ℝ))) * max 0 C₂ := by
              gcongr
            _ ≤ productBound hstar a b *
                  (max 0 C₁ * ρ ^ (γ - (c : ℝ))) * max 0 C₂ := by
              gcongr
            _ = (productBound hstar a b * max 0 C₁ * max 0 C₂) *
                  ρ ^ (γ - (c : ℝ)) := by ring
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (productBound_nonneg hstar a b) (le_max_left 0 C₁))
            (le_max_left 0 C₂))
          (Real.rpow_nonneg hρ0 _)
    _ = (∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
          productBound hstar a b * max 0 C₁ * max 0 C₂) *
          ρ ^ (γ - (c : ℝ)) := by
      simp_rw [Finset.sum_mul]

private lemma product_difference_bound
    {d : ℕ} {s : Fin d → ℕ}
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    {V W : ∀ a : A, Submodule ℝ (E a)}
    {α₁ α₂ γ₁ γ₂ γ : ℝ}
    (hV : IsSector G V α₁) (hW : IsSector G W α₂)
    (hγ : γ = min (γ₁ + α₂) (γ₂ + α₁))
    {f₁ f₂ : Pt d → ModelSpace A E}
    (hf₁ : IsModelled s γ₁ Gam f₁) (hf₁V : TakesValuesIn V f₁)
    (hf₂ : IsModelled s γ₂ Gam f₂) (hf₂W : TakesValuesIn W f₂)
    {K : Set (Pt d)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, snorm s (x - y) ≤ 1 →
      ∀ c : A, (c : ℝ) < γ →
      ‖proj c (star (f₁ x) (f₂ x) -
        star (Gam x y (f₁ y)) (Gam x y (f₂ y)))‖ ≤
          C * snorm s (x - y) ^ (γ - (c : ℝ)) := by
  obtain ⟨C₁, hf₁val, hf₁inc⟩ := hf₁.bound K hK
  obtain ⟨C₂, hf₂val, hf₂inc⟩ := hf₂.bound K hK
  let D₁ := ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
    productBound hstar a b * max 0 C₁ * max 0 C₂
  let D₂ := ∑ b ∈ degreesLT hT γ₂, ∑ a ∈ degreesLT hT γ₁,
    productBound hstar.flip b a * max 0 C₂ * max 0 (2 * max 0 C₁)
  refine ⟨D₁ + D₂, ?_⟩
  intro x hx y hy hρ c hc
  let ρ := snorm s (x - y)
  have hρ0 : 0 ≤ ρ := snorm_nonneg s _
  have hγleft : γ ≤ γ₁ + α₂ := by rw [hγ]; exact min_le_left _ _
  have hγright : γ ≤ γ₂ + α₁ := by rw [hγ]; exact min_le_right _ _
  have hf₁x0 : ∀ a : A, γ₁ ≤ (a : ℝ) → proj a (f₁ x) = 0 := hf₁.vanishing x
  have hf₂x0 : ∀ b : A, γ₂ ≤ (b : ℝ) → proj b (f₂ x) = 0 := hf₂.vanishing x
  have hgf₁y0 : ∀ a : A, γ₁ ≤ (a : ℝ) → proj a (Gam x y (f₁ y)) = 0 :=
    gam_vanishing hT hmod hf₁ x y
  have hgf₂y0 : ∀ b : A, γ₂ ≤ (b : ℝ) → proj b (Gam x y (f₂ y)) = 0 :=
    gam_vanishing hT hmod hf₂ x y
  have hdf₁0 : ∀ a : A, γ₁ ≤ (a : ℝ) →
      proj a (f₁ x - Gam x y (f₁ y)) = 0 := by
    intro a ha
    simp [hf₁x0 a ha, hgf₁y0 a ha]
  have hdf₂0 : ∀ b : A, γ₂ ≤ (b : ℝ) →
      proj b (f₂ x - Gam x y (f₂ y)) = 0 := by
    intro b hb
    simp [hf₂x0 b hb, hgf₂y0 b hb]
  have hf₂low : ∀ b : A, (b : ℝ) < α₂ → proj b (f₂ x) = 0 := by
    intro b hb
    have hm := hf₂W x b
    rw [hW.vanishing b hb] at hm
    simpa using hm
  have hgf₁sector : Gam x y (f₁ y) ∈ sectorSpace V :=
    hV.invariant (Gam x y) (hmod.gam_mem x y) (f₁ y) (hf₁V y)
  have hgf₁low : ∀ a : A, (a : ℝ) < α₁ → proj a (Gam x y (f₁ y)) = 0 := by
    intro a ha
    have hm := hgf₁sector a
    rw [hV.vanishing a ha] at hm
    simpa using hm
  have hgf₁bound : ∀ a : A, (a : ℝ) < γ₁ →
      ‖proj a (Gam x y (f₁ y))‖ ≤ 2 * max 0 C₁ := by
    intro a ha
    have hpow : ρ ^ (γ₁ - (a : ℝ)) ≤ 1 :=
      Real.rpow_le_one hρ0 hρ (by linarith)
    have hval : ‖proj a (f₁ x)‖ ≤ max 0 C₁ :=
      (hf₁val x hx a ha).trans (le_max_right 0 C₁)
    have hinc : ‖proj a (f₁ x - Gam x y (f₁ y))‖ ≤
        max 0 C₁ * ρ ^ (γ₁ - (a : ℝ)) :=
      (hf₁inc x hx y hy hρ a ha).trans (by
        gcongr
        exact le_max_right 0 C₁)
    have heq : proj a (Gam x y (f₁ y)) =
        proj a (f₁ x) - proj a (f₁ x - Gam x y (f₁ y)) := by
      simp
    rw [heq]
    calc
      ‖proj a (f₁ x) - proj a (f₁ x - Gam x y (f₁ y))‖ ≤
          ‖proj a (f₁ x)‖ + ‖proj a (f₁ x - Gam x y (f₁ y))‖ := norm_sub_le _ _
      _ ≤ max 0 C₁ + max 0 C₁ * ρ ^ (γ₁ - (a : ℝ)) := add_le_add hval hinc
      _ ≤ 2 * max 0 C₁ := by nlinarith [le_max_left 0 C₁]
  have hfirst := first_increment_bound hT hstar
    (f₁ x - Gam x y (f₁ y)) (f₂ x) hdf₁0 hf₂x0
    (fun a ha => hf₁inc x hx y hy hρ a ha)
    (fun b hb => hf₂val x hx b hb) hf₂low hγleft hρ0 hρ c hc
  have hsecond := first_increment_bound hT hstar.flip
    (f₂ x - Gam x y (f₂ y)) (Gam x y (f₁ y)) hdf₂0 hgf₁y0
    (fun b hb => hf₂inc x hx y hy hρ b hb) hgf₁bound hgf₁low
    hγright hρ0 hρ c hc
  have hdiff :
      star (f₁ x) (f₂ x) - star (Gam x y (f₁ y)) (Gam x y (f₂ y)) =
        star (f₁ x - Gam x y (f₁ y)) (f₂ x) +
          star (Gam x y (f₁ y)) (f₂ x - Gam x y (f₂ y)) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [hdiff, map_add]
  calc
    ‖proj c (star (f₁ x - Gam x y (f₁ y)) (f₂ x)) +
        proj c (star (Gam x y (f₁ y)) (f₂ x - Gam x y (f₂ y)))‖ ≤
      ‖proj c (star (f₁ x - Gam x y (f₁ y)) (f₂ x))‖ +
        ‖proj c (star (Gam x y (f₁ y)) (f₂ x - Gam x y (f₂ y)))‖ := norm_add_le _ _
    _ ≤ D₁ * ρ ^ (γ - (c : ℝ)) + D₂ * ρ ^ (γ - (c : ℝ)) :=
      add_le_add hfirst hsecond
    _ = (D₁ + D₂) * snorm s (x - y) ^ (γ - (c : ℝ)) := by
      dsimp only [ρ]
      ring

private lemma fixedTruncProd_component_bound
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {d : ℕ} {s : Fin d → ℕ} {γ γ₁ γ₂ : ℝ}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    {f g : Pt d → ModelSpace A E}
    (hf : IsModelled s γ₁ Gam f) (hg : IsModelled s γ₂ Gam g)
    {K : Set (Pt d)} {C₁ C₂ : ℝ}
    (hfK : ∀ x ∈ K, ∀ b : A, (b : ℝ) < γ₁ → ‖proj b (f x)‖ ≤ C₁)
    (hgK : ∀ x ∈ K, ∀ b : A, (b : ℝ) < γ₂ → ‖proj b (g x)‖ ≤ C₂) :
    ∀ x ∈ K, ∀ c : A,
      ‖proj c (fixedTruncProd hT γ γ₁ γ₂ star f g x)‖ ≤
        ∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
          productBound hstar m n * max 0 C₁ * max 0 C₂ := by
  intro x hx c
  simp only [fixedTruncProd, map_sum]
  calc
    ‖∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
        proj c (if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0)‖ ≤
      ∑ m ∈ degreesLT hT γ₁, ‖∑ n ∈ degreesLT hT γ₂,
        proj c (if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
        ‖proj c (if (m : ℝ) + (n : ℝ) < γ then
          star (incl m (proj m (f x))) (incl n (proj n (g x))) else 0)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ degreesLT hT γ₁, ∑ n ∈ degreesLT hT γ₂,
        productBound hstar m n * max 0 C₁ * max 0 C₂ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hmn
      · rw [show proj c (star (incl m (proj m (f x)))
            (incl n (proj n (g x)))) =
            proj c (star (incl m (proj m (f x)))
              (incl n (proj n (g x)))) by rfl]
        calc
          ‖proj c (star (incl m (proj m (f x)))
              (incl n (proj n (g x))))‖ ≤
              productBound hstar m n * ‖proj m (f x)‖ * ‖proj n (g x)‖ :=
            product_bound hstar m n c _ _
          _ ≤ productBound hstar m n * max 0 C₁ * max 0 C₂ := by
            have hB : 0 ≤ productBound hstar m n :=
              productBound_nonneg hstar m n
            have hf' : ‖proj m (f x)‖ ≤ max 0 C₁ :=
              (hfK x hx m (mem_degreesLT hT γ₁ m |>.mp hm)).trans
                (le_max_right 0 C₁)
            have hg' : ‖proj n (g x)‖ ≤ max 0 C₂ :=
              (hgK x hx n (mem_degreesLT hT γ₂ n |>.mp hn)).trans
                (le_max_right 0 C₂)
            calc
              productBound hstar m n * ‖proj m (f x)‖ * ‖proj n (g x)‖ ≤
                  productBound hstar m n * max 0 C₁ * ‖proj n (g x)‖ := by
                gcongr
              _ ≤ productBound hstar m n * max 0 C₁ * max 0 C₂ := by
                gcongr
      · simp only [map_zero, norm_zero]
        exact mul_nonneg (mul_nonneg (productBound_nonneg hstar m n)
          (le_max_left 0 C₁)) (le_max_left 0 C₂)

lemma truncProd_vanishing {d : ℕ} {γ : ℝ}
    {one : ModelSpace A E}
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    {f g : Pt d → ModelSpace A E} (hstar : IsProduct one star) :
    ∀ (x : Pt d) (c : A), γ ≤ (c : ℝ) →
      proj c (truncProd γ star f g x) = 0 := by
  intro x c hc
  simp only [truncProd, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  split_ifs with hmn
  · exact hstar.graded m n c (proj m (f x)) (proj n (g x)) (by linarith)
  · exact map_zero (proj c)

end Hairer

open Hairer

theorem solution {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type}
    [∀ a : A, NormedAddCommGroup (E a)] [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)}
    {one : ModelSpace A E} (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    {V W : ∀ a : A, Submodule ℝ (E a)}
    {α₁ α₂ : ℝ} (hV : IsSector G V α₁) (hW : IsSector G W α₂)
    {γ₁ γ₂ γ : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hγ : γ = min (γ₁ + α₂) (γ₂ + α₁))
    (hreg : IsGammaRegular G V W star γ)
    {f₁ f₂ : Pt d → ModelSpace A E}
    (hf₁ : IsModelled s γ₁ Gam f₁) (hf₁V : TakesValuesIn V f₁)
    (hf₂ : IsModelled s γ₂ Gam f₂) (hf₂W : TakesValuesIn W f₂) :
    IsModelled s γ Gam (truncProd γ star f₁ f₂) := by
  constructor
  · exact truncProd_vanishing hstar
  · intro K hK
    obtain ⟨C₁, hf₁val, _⟩ := hf₁.bound K hK
    obtain ⟨C₂, hf₂val, _⟩ := hf₂.bound K hK
    let Cval := ∑ a ∈ degreesLT hT γ₁, ∑ b ∈ degreesLT hT γ₂,
      productBound hstar a b * max 0 C₁ * max 0 C₂
    have hval := fixedTruncProd_component_bound (γ := γ) hT hstar
      hf₁ hf₂ hf₁val hf₂val
    obtain ⟨Cdif, hdif⟩ :=
      product_difference_bound hT hmod hstar hV hW hγ hf₁ hf₁V hf₂ hf₂W hK
    obtain ⟨Ccor, hcor⟩ :=
      truncation_correction_bound hT hmod hstar hγ₁ hγ₂ hreg hf₁ hf₁V hf₂ hf₂W hK
    refine ⟨max Cval (Cdif + Ccor), ?_, ?_⟩
    · intro x hx c hc
      rw [truncProd_eq_fixedTruncProd hT hf₁ hf₂]
      exact (hval x hx c).trans (le_max_left Cval (Cdif + Ccor))
    · intro x hx y hy hρ c hc
      let Fxy := star (Gam x y (f₁ y)) (Gam x y (f₂ y))
      have heq :
          proj c (truncProd γ star f₁ f₂ x -
            Gam x y (truncProd γ star f₁ f₂ y)) =
            proj c (star (f₁ x) (f₂ x) - Fxy) +
              proj c (Fxy - Gam x y (truncProd γ star f₁ f₂ y)) := by
        simp only [map_sub, Fxy]
        rw [truncProd_component_eq_full hstar f₁ f₂ x c hc]
        abel
      rw [heq]
      calc
        ‖proj c (star (f₁ x) (f₂ x) - Fxy) +
            proj c (Fxy - Gam x y (truncProd γ star f₁ f₂ y))‖ ≤
          ‖proj c (star (f₁ x) (f₂ x) - Fxy)‖ +
            ‖proj c (Fxy - Gam x y (truncProd γ star f₁ f₂ y))‖ :=
          norm_add_le _ _
        _ ≤ Cdif * snorm s (x - y) ^ (γ - (c : ℝ)) +
              Ccor * snorm s (x - y) ^ (γ - (c : ℝ)) := by
          exact add_le_add (hdif x hx y hy hρ c hc) (hcor x hx y hy hρ c hc)
        _ = (Cdif + Ccor) * snorm s (x - y) ^ (γ - (c : ℝ)) := by ring
        _ ≤ max Cval (Cdif + Ccor) * snorm s (x - y) ^ (γ - (c : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right Cval (Cdif + Ccor))
            (Real.rpow_nonneg (snorm_nonneg s _) _)
