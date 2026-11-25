-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:30.897842+00:00
-- url     : https://prove2.me/submissions/7811fe22-e4b4-4fb1-ad7a-9ba9181650d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_isHomogeneous_ker_coneHom
import Theorems.Thm_GlobalTheory_ZH_ConePrime_ringKrullDim_quotient_ker
import Theorems.Thm_GlobalTheory_ZH_ConePrime_exists_generic
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_injective
import Theorems.Thm_GlobalTheory_ZH_ConePrime_vanishingIdeal_eq_ker
import Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_affineOpen
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_exists
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_isUnit_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_ratio
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → IsIntegral X → ∀ g : ℕ, SmoothOfRelativeDimension g p → (MvPolynomial.vanishingIdeal k (cone p H s)).IsPrime ∧ (MvPolynomial.vanishingIdeal k (cone p H s)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) ∧ (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k (cone p H s)) ∧ ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k (cone p H s)) = (g + 1 : ℕ)) := by
  intro k _ _ X p H J _ s J₀ hH him hX g hg
  have : genericPoint X ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by rw [him.1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi, hm⟩ := this
  obtain ⟨haff, r, hr, hc⟩ := him.2 i hi
  haveI : Nonempty (Out.nonzeroLocus (s i)) := ⟨⟨_, hm⟩⟩
  rw [vanishingIdeal_eq_ker p hH him i haff ⟨_, hm⟩ r hr hc]
  have hri : r i = 1 := by
    obtain ⟨K, _, y, hy⟩ := exists_generic (X := X)
    obtain ⟨w, hw⟩ := crd_exists hH s y
    have h := hy _ ⟨_, hm⟩
    have hu : w i ≠ 0 := ((crd_isUnit_iff i hw).2 h).ne_zero
    apply valHom_injective y hy _ h
    have := crd_ratio hw (hr i) h
    rw [valR_eq y _ h] at this
    rw [map_one]
    exact mul_right_cancel₀ hu (by rw [← this, _root_.one_mul])
  refine ⟨RingHom.ker_isPrime _, isHomogeneous_ker_coneHom _ _, ⟨i, ?_⟩, ?_⟩
  · simp [RingHom.mem_ker, coneHom, hri]
  · letI : Algebra k Γ(X, Out.nonzeroLocus (s i)) := (constHom p _).toAlgebra
    exact ringKrullDim_quotient_ker (k := k) r i hri hc g
      (GlobalTheory.SmoothDim.ringKrullDim_affineOpen k X p g hg _ haff ⟨_, hm⟩)
end GlobalTheory.ZH.ConePrime
