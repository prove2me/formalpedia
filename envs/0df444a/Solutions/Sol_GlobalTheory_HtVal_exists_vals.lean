-- Prove2me | solution 1 for GlobalTheory.HtVal.exists_vals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:58.916019+00:00
-- url     : https://prove2.me/submissions/c9025090-0e7b-431a-8e62-1877f0f7f8bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup
import Theorems.Thm_GlobalTheory_HtVal_exists_val
import Theorems.Thm_GlobalTheory_HtVal_val_eq_zero_of_notMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_finite_height_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_mem_range_of_forall_height_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HtVal
namespace GlobalTheory.HtVal
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  intro R _ _ _ _ J _ g
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
        0 ≤ Multiplicative.toAdd (w x) ↔
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range :=
    fun P _ h1 => exists_val R P h1
  choose W hW using key
  have hsurj := fun j => IsLocalization.surj (nonZeroDivisors R) (g j : FractionRing R)
  choose nd hnd using hsurj
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hd0 : ∀ j, ((nd j).2 : R) ≠ 0 := fun j => nonZeroDivisors.coe_ne_zero _
  have hn0 : ∀ j, (nd j).1 ≠ 0 := by
    intro j h
    have := hnd j
    rw [h, map_zero] at this
    exact (mul_ne_zero (g j).ne_zero ((map_ne_zero_iff _ hinj).2 (hd0 j))) this
  have hc0 : (∏ j, (nd j).1 * ((nd j).2 : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hn0 j) (hd0 j)
  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one hc0
  let T := hfin.toFinset
  let e := T.equivFin.symm
  have hmemT : ∀ i : Fin T.card, (e i : Ideal R).IsPrime ∧ (e i : Ideal R).height = 1 ∧
      (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ (e i : Ideal R) := fun i => hfin.mem_toFinset.1 (e i).2
  refine ⟨T.card, fun i => W (e i) (hmemT i).1 (hmemT i).2.1, ?_, ?_⟩
  · intro i x r hx
    refine (hW _ _ _ x).2 ⟨1, fun h => (hmemT i).1.ne_top ((Ideal.eq_top_iff_one _).2 h), r, ?_⟩
    rw [map_one, one_mul, hx]
  · intro x hx hv
    refine (fun h => ⟨h.choose, h.choose_spec.symm⟩)
      (ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (x : FractionRing R) ?_)
    intro P hP h1
    by_cases hcP : (∏ j, (nd j).1 * ((nd j).2 : R)) ∈ P
    · obtain ⟨i, hi⟩ := e.surjective ⟨P, hfin.mem_toFinset.2 ⟨hP, h1, hcP⟩⟩
      have gen : ∀ (Q : Ideal R) (hQ : Q.IsPrime) (hQ1 : Q.height = 1), Q = P →
          0 ≤ Multiplicative.toAdd (W Q hQ hQ1 x) →
          ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
        rintro Q hQ hQ1 rfl h
        exact (hW Q hQ hQ1 x).1 h
      exact gen _ _ _ (congrArg Subtype.val hi) (hv i)
    · have hnP : ∀ j, (nd j).1 ∉ P ∧ ((nd j).2 : R) ∉ P := by
        intro j
        obtain ⟨k, hk⟩ : (nd j).1 * ((nd j).2 : R) ∣ ∏ j, (nd j).1 * ((nd j).2 : R) :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        refine ⟨fun h => hcP ?_, fun h => hcP ?_⟩
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_right _ h)
        · rw [hk]; exact P.mul_mem_right k (P.mul_mem_left _ h)
      have hker : Subgroup.closure (Set.range g) ≤ (W P hP h1).ker := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        let un : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ (nd j).1) ((map_ne_zero_iff _ hinj).2 (hn0 j))
        let ud : (FractionRing R)ˣ := Units.mk0 (algebraMap R _ ((nd j).2 : R)) ((map_ne_zero_iff _ hinj).2 (hd0 j))
        have hgu : g j = un * ud⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact Units.ext (hnd j)
        have hn := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) un _ rfl (hnP j).1
        have hd := val_eq_zero_of_notMem R P (W P hP h1) (hW P hP h1) ud _ rfl (hnP j).2
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hgu, map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, hn, hd, toAdd_one]
        simp
      have h0 : W P hP h1 x = 1 := hker hx
      exact (hW P hP h1 x).1 (by rw [h0, toAdd_one])
end GlobalTheory.HtVal
