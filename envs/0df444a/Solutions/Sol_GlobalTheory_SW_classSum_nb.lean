-- Prove2me | solution 1 for GlobalTheory.SW.classSum_nb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:48.534858+00:00
-- url     : https://prove2.me/submissions/c98568e4-0dcc-48ff-a133-28c8cb72c639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_NbAvg_wt_mul_nbIn
import Theorems.Thm_GlobalTheory_SW_NbAvg_sum_nb
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_GlobalTheory_SW_neighbours


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open NbAvg
namespace GlobalTheory.SW
theorem _root_.solution :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  intro E _ _ _ n M q P hM hP f hf
  obtain ⟨hcls, -, -, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have hf' : IsClassFn M f := hf
  have hone : IsClassFn M (fun _ : Lt E n => (1 : ℂ)) := fun _ _ _ _ _ _ _ => rfl
  have hcount : ∀ d : Cls E n M, ((q : ℂ) - 1) *
      ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ) =
      (q : ℂ) ^ n - 1 := by
    intro d
    obtain ⟨hfin, hcnt, -⟩ := hnb' _ (Quot.out d).2
    have hs := NbAvg.sum_nb hfin hone
    simp only [mul_one] at hs
    have h1 : ∑ᶠ X ∈ Nb M (conjI P) (Quot.out d).1, (1 : ℂ) =
        ((Nb M (conjI P) (Quot.out d).1).ncard : ℂ) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul, mul_one,
        Set.ncard_eq_toFinset_card _ hfin]
    rw [h1] at hs
    rw [← hs]
    have hq1 : 1 ≤ q := hP.1.one_lt.le
    have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ hP.1.pos
    have hc := congrArg (fun x : ℕ => (x : ℂ)) hcnt
    simp only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hqn, Nat.cast_pow, Nat.cast_one] at hc
    linear_combination hc
  have hsum : ∀ c : Cls E n M, ∑ᶠ X ∈ Nb M P (Quot.out c).1, f X =
      ∑ d : Cls E n M, ((nbIn M P (Quot.out c).1 (Quot.out d).1).ncard : ℂ) * f (Quot.out d).1 :=
    fun c => NbAvg.sum_nb (hnb _ (Quot.out c).2).1 hf'
  simp only [classSum, finsum_eq_sum_of_fintype, hsum]
  calc _ = ∑ c : Cls E n M, ∑ d : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← wt_mul_nbIn hM hP (Quot.out c).2 (Quot.out d).2]
        ring
    _ = ∑ d : Cls E n M, ∑ c : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 :=
        Finset.sum_comm
    _ = ∑ d : Cls E n M, ((wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1) * (((q : ℂ) - 1) *
        ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ((q : ℂ) ^ n - 1) * ∑ d : Cls E n M, (wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hcount d]
        ring
end GlobalTheory.SW
