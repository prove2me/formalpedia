-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.conv_of_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:40.823085+00:00
-- url     : https://prove2.me/submissions/09b17231-dad0-4ff0-bc0f-0bb4a7ec189b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_stab_of_cGL
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_rat
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_ht_law
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_ht_cGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (x : ℝ)
    (hx : Conv (A.ratGL (Sub ι m)) (stab R ({t₀} : Set (Sub ι m))) fun g => x * A.htGL ({t₀} : Set (Sub ι m)) g) :
    Conv (A.ratGL ι) (stab R (t₀.1 : Set ι)) fun g => x * A.htGL (t₀.1 : Set ι) g := by
  intro g
  let Φ : Cos (stab R (t₀.1 : Set ι)) (A.ratGL ι) → Cos (stab R ({t₀} : Set (Sub ι m))) (A.ratGL (Sub ι m)) :=
    fun q => Quotient.mk _ ⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩
  have hinj : Function.Injective Φ := by
    intro q₁ q₂ h
    have h1 := Quotient.exact h
    change QuotientGroup.rightRel _ _ _ at h1
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h1
    have h2 : cGL m (rep q₂ * (rep q₁)⁻¹) ∈ stab R ({t₀} : Set (Sub ι m)) := by
      rw [map_mul, map_inv]
      exact h1
    have h3 : rep q₂ * (rep q₁)⁻¹ ∈ A.ratGL ι := mul_mem (Quotient.out q₂).2 (inv_mem (Quotient.out q₁).2)
    have h4 := stab_of_cGL A hA.iinj h3 h2
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    refine Quotient.sound ?_
    change QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
    exact h4
  have hval : ∀ q, rep (Φ q) * cGL m g = (rep (Φ q) * (cGL m (rep q))⁻¹) * cGL m (rep q * g) := by
    intro q
    rw [map_mul]
    group
  have hmem : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ stab R ({t₀} : Set (Sub ι m)) := by
    intro q
    have h1 := Quotient.mk_out (s := QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m))))
      (⟨cGL m (rep q), cGL_rat A (Quotient.out q).2⟩ : A.ratGL (Sub ι m))
    have h2 := (QuotientGroup.rightRel ((stab R ({t₀} : Set (Sub ι m))).subgroupOf (A.ratGL (Sub ι m)))).iseqv.symm h1
    change QuotientGroup.rightRel _ _ _ at h2
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hrat : ∀ q, rep (Φ q) * (cGL m (rep q))⁻¹ ∈ A.ratGL (Sub ι m) := fun q =>
    mul_mem (Quotient.out (Φ q)).2 (inv_mem (cGL_rat A (Quotient.out q).2))
  have H := ht_law hB hE A hA (Sub ι m) ({t₀} : Set (Sub ι m))
  have hs := (hx (cGL m g)).comp_injective hinj
  refine hs.congr fun q => ?_
  simp only [Function.comp_apply]
  rw [hval q, H.1.left _ (hmem q), H.1.rat _ (hrat q) (hmem q), zero_add, ht_cGL hB hE A hA]
end GlobalTheory.CompanionTheory.Plucker
