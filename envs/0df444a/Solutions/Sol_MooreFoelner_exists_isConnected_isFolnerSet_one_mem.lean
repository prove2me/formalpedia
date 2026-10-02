-- Prove2me | solution 1 for MooreFoelner.exists_isConnected_isFolnerSet_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T06:47:39.225396+00:00
-- url     : https://prove2.me/submissions/34c90322-01e0-4b0a-8646-75a4b9b62788

import Theorems.Thm_MooreFoelner_exists_isConnectedComponent_isWeightedFolner
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §3 (group Sec3B): Remark 3.8, Lemmas 3.10, 3.12, 3.14, 3.15
-/

namespace MooreFoelner.Dev.Sec3B

open Classical MooreFoelner

set_option linter.unusedSectionVars false

variable {G S : Type*} [Group G]

/-! ## Marginal sets -/

/-! ## Mass, restriction and `valAt` -/

theorem mass_univ (μ : S →₀ ℝ) : mass μ Set.univ = ∑ s ∈ μ.support, μ s := by
  simp [mass]

theorem mass_nonneg {μ : S →₀ ℝ} (hμ : ∀ s, 0 ≤ μ s) (A : Set S) : 0 ≤ mass μ A :=
  Finset.sum_nonneg fun s _ => hμ s

theorem restrict_apply (μ : S →₀ ℝ) (A : Set S) (s : S) :
    restrict μ A s = if s ∈ A then μ s else 0 := by
  simp [restrict, Finsupp.filter_apply]

theorem valAt_of_some {act : S → G → Option S} {μ : S →₀ ℝ} {s y : S} {g : G}
    (h : act s g = some y) : valAt act μ s g = μ y := by
  simp [valAt, h]

/-! ## Weighted Følner sets -/

theorem wf_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < ε * mass μ Set.univ :=
  lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => finsum_nonneg fun _ => abs_nonneg _) h.2

theorem wf_mass_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < mass μ Set.univ := by
  have h1 := wf_pos h
  have h2 := mass_nonneg h.1 Set.univ
  rcases h2.lt_or_eq with h2 | h2
  · exact h2
  · rw [← h2, mul_zero] at h1; exact absurd h1 (lt_irrefl _)

theorem wf_eps_pos {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ}
    (h : IsWeightedFolner act Γ μ ε) : 0 < ε := by
  have h1 := wf_pos h
  have h2 := wf_mass_pos h
  by_contra hε
  push Not at hε
  nlinarith

/-! ## Lemma 3.10 -/

/-! ## Γ-connected sets and components -/

/-- One step of a chain inside `A`. -/
def Step (act : S → G → Option S) (Γ : Finset G) (A : Set S) (x y : S) : Prop :=
  x ∈ A ∧ y ∈ A ∧ ∃ γ ∈ Γ, act x γ = some y

theorem isConnected_iff (act : S → G → Option S) (Γ : Finset G) (A : Set S) :
    IsConnected act Γ A ↔ ∀ x ∈ A, ∀ y ∈ A, Relation.ReflTransGen (Step act Γ A) x y := by
  constructor
  · intro h x hx y hy
    obtain ⟨l, p, h0, hl, hA, hstep⟩ := h x hx y hy
    have : ∀ i : Fin (l + 1), Relation.ReflTransGen (Step act Γ A) x (p i) := by
      intro i
      induction i using Fin.induction with
      | zero => rw [h0]
      | succ i ih =>
        obtain ⟨γ, hγ, h⟩ := hstep i
        exact ih.tail ⟨hA _, hA _, γ, hγ, h⟩
    simpa [hl] using this (Fin.last l)
  · intro h x hx y hy
    have key : ∀ z, Relation.ReflTransGen (Step act Γ A) x z → ∃ (l : ℕ) (p : Fin (l + 1) → S),
        p 0 = x ∧ p (Fin.last l) = z ∧ (∀ i, p i ∈ A) ∧
          ∀ i : Fin l, ∃ γ ∈ Γ, act (p i.castSucc) γ = some (p i.succ) := by
      intro z hz
      induction hz with
      | refl => exact ⟨0, fun _ => x, rfl, rfl, fun _ => hx, fun i => i.elim0⟩
      | @tail b c _ hbc ih =>
        obtain ⟨l, p, h0, hl, hA, hstep⟩ := ih
        obtain ⟨_, hc, γ, hγ, hbc'⟩ := hbc
        refine ⟨l + 1, Fin.snoc p c, ?_, ?_, ?_, ?_⟩
        · have : (0 : Fin (l + 2)) = Fin.castSucc (0 : Fin (l + 1)) := rfl
          rw [this, Fin.snoc_castSucc, h0]
        · rw [Fin.snoc_last]
        · intro i
          induction i using Fin.lastCases with
          | last => rw [Fin.snoc_last]; exact hc
          | cast i => rw [Fin.snoc_castSucc]; exact hA i
        · intro i
          induction i using Fin.lastCases with
          | last =>
            refine ⟨γ, hγ, ?_⟩
            have : (Fin.last l).succ = Fin.last (l + 1) := Fin.succ_last l
            rw [Fin.snoc_castSucc, this, Fin.snoc_last, hl]
            exact hbc'
          | cast i =>
            obtain ⟨γ', hγ', h'⟩ := hstep i
            refine ⟨γ', hγ', ?_⟩
            rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
            exact h'
    exact key y (h x hx y hy)

section comp

variable {act : S → G → Option S} {Γ : Finset G} {μ : S →₀ ℝ}

end comp

/-! ## The right action of `G` on itself -/

theorem isPartialAction_rightMul : IsPartialAction (rightMul (G := G)) where
  one x := by simp [rightMul]
  inv g x y := by
    simp only [rightMul, Option.some.injEq]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  mul g h x y z hxy hyz := by
    simp only [rightMul, Option.some.injEq] at *
    subst hxy; subst hyz; simp [mul_assoc]

theorem indicator_apply (A : Finset S) (s : S) : indicator A s = if s ∈ A then 1 else 0 := by
  simp [indicator, Finsupp.onFinset_apply]

theorem support_indicator (A : Finset S) : (indicator A).support = A := by
  ext s
  rw [Finsupp.mem_support_iff, indicator_apply]
  split_ifs with h <;> simp [h]

theorem mass_indicator (A : Finset S) : mass (indicator A) Set.univ = A.card := by
  rw [mass_univ, support_indicator,
    Finset.sum_congr rfl (fun s hs => by rw [indicator_apply, if_pos hs])]
  simp

open scoped symmDiff in
theorem finsum_indicator (A : Finset G) (γ : G) :
    ∑ᶠ s, |valAt rightMul (indicator A) s γ - indicator A s| =
      ((A.image (· * γ)) ∆ A).card := by
  have h1 : ∀ s, valAt rightMul (indicator A) s γ = indicator A (s * γ) :=
    fun s => valAt_of_some rfl
  simp_rw [h1]
  rw [← finsum_comp_equiv (Equiv.mulRight γ⁻¹)]
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right]
  have h2 : ∀ t, |indicator A t - indicator A (t * γ⁻¹)| =
      if t ∈ (A.image (· * γ)) ∆ A then 1 else 0 := by
    intro t
    rw [indicator_apply, indicator_apply]
    by_cases ht : t ∈ A <;> by_cases ht' : t * γ⁻¹ ∈ A <;>
      simp [Finset.mem_symmDiff, ht, ht']
  simp_rw [h2]
  rw [finsum_eq_sum_of_support_subset (s := (A.image (· * γ)) ∆ A)]
  · simp
  · intro t ht
    by_contra h
    exact ht (if_neg h)

theorem isWeightedFolner_indicator_iff (Γ A : Finset G) (ε : ℝ) :
    IsWeightedFolner rightMul Γ (indicator A) ε ↔ IsFolnerSet Γ A ε := by
  have hnn : ∀ s, 0 ≤ indicator A s := fun s => by
    rw [indicator_apply]; split_ifs <;> norm_num
  simp only [IsWeightedFolner, IsFolnerSet, finsum_indicator, mass_indicator]
  exact ⟨fun h => h.2, fun h => ⟨hnn, h⟩⟩

theorem restrict_indicator (A : Finset S) (C : Set S) :
    restrict (indicator A) C = indicator (A.filter (· ∈ C)) := by
  ext s
  rw [restrict_apply, indicator_apply, indicator_apply]
  by_cases h1 : s ∈ A <;> by_cases h2 : s ∈ C <;> simp [h1, h2, Finset.mem_filter]

open scoped symmDiff in
theorem isFolnerSet_translate {Γ C : Finset G} {ε : ℝ} (h : IsFolnerSet Γ C ε) (g : G) :
    IsFolnerSet Γ (C.image (g * ·)) ε := by
  have hinj : Function.Injective (g * · : G → G) := mul_right_injective g
  have key : ∀ γ, ((C.image (g * ·)).image (· * γ) ∆ C.image (g * ·)).card =
      ((C.image (· * γ)) ∆ C).card := by
    intro γ
    have hc : ((fun x => x * γ) ∘ fun x => g * x) = ((fun x => g * x) ∘ fun x => x * γ) := by
      funext x; simp [mul_assoc]
    have he : (C.image (g * ·)).image (· * γ) ∆ C.image (g * ·) =
        ((C.image (· * γ)) ∆ C).image (g * ·) := by
      rw [Finset.image_symmDiff _ _ hinj, Finset.image_image, Finset.image_image, hc]
    rw [he, Finset.card_image_of_injective _ hinj]
  unfold IsFolnerSet at h ⊢
  rw [Finset.card_image_of_injective _ hinj]
  simp_rw [key]
  exact h

theorem isConnected_translate {Γ C : Finset G} (h : IsConnected rightMul Γ ↑C) (g : G) :
    IsConnected rightMul Γ ↑(C.image (g * ·)) := by
  rw [isConnected_iff] at h ⊢
  intro x hx y hy
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  refine Relation.ReflTransGen.lift (g * ·) (fun a b hab => ?_) x y (h x hx y hy)
  obtain ⟨ha, hb, γ, hγ, hab⟩ := hab
  simp only [rightMul, Option.some.injEq] at hab
  refine ⟨?_, ?_, γ, hγ, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha)
  · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hb)
  · simp [rightMul, ← hab, mul_assoc]

end MooreFoelner.Dev.Sec3B

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Sec3B in
theorem solution {G : Type*} [Group G] (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ)
    (A : Finset G) (hA : IsFolnerSet Γ A ε) :
    ∃ B : Finset G, IsFolnerSet Γ B ε ∧ IsConnected rightMul Γ ↑B ∧ (1 : G) ∈ B ∧
      B.card ≤ A.card := by
  have hW : IsWeightedFolner rightMul Γ (indicator A) ε :=
    (isWeightedFolner_indicator_iff Γ A ε).mpr hA
  have hε := wf_eps_pos hW
  obtain ⟨C, hC, hCW⟩ := exists_isConnectedComponent_isWeightedFolner rightMul
    isPartialAction_rightMul Γ hsymm hgen ε hε (indicator A) hW
  set C' := A.filter (· ∈ C) with hC'
  have hCC' : (↑C' : Set G) = C := by
    ext x
    simp only [hC', Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by simpa [support_indicator] using hC.1 hx, hx⟩
  rw [restrict_indicator] at hCW
  have hC'F : IsFolnerSet Γ C' ε := (isWeightedFolner_indicator_iff Γ C' ε).mp hCW
  have hne : C'.Nonempty := by
    have := wf_mass_pos hCW
    rw [mass_indicator] at this
    exact Finset.card_pos.mp (by exact_mod_cast this)
  obtain ⟨g, hg⟩ := hne
  refine ⟨C'.image (g⁻¹ * ·), isFolnerSet_translate hC'F g⁻¹, ?_, ?_, ?_⟩
  · apply isConnected_translate
    rw [hCC']
    exact hC.2.1
  · exact Finset.mem_image.mpr ⟨g, hg, inv_mul_cancel g⟩
  · rw [Finset.card_image_of_injective _ (mul_right_injective g⁻¹)]
    exact Finset.card_filter_le _ _
