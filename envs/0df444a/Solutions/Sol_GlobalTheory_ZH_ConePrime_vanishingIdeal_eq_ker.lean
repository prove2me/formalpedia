-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.vanishingIdeal_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:05.987261+00:00
-- url     : https://prove2.me/submissions/779d7d8c-3235-4fdd-8ece-0b76f5cd93f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd
import Theorems.Thm_GlobalTheory_ZH_ConePrime_eq_zero_of_forall_algHom
import Theorems.Thm_GlobalTheory_ZH_ConePrime_finiteType_of_closure
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_comp_constHom
import Theorems.Thm_GlobalTheory_ZH_ConePrime_exists_point
import Theorems.Thm_GlobalTheory_ZH_ConePrime_exists_generic
import Theorems.Thm_GlobalTheory_ZH_ConePrime_coneHom_eq_zero_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_exists
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_isUnit_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_ratio
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_smul
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_top_le_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_eq
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
variable {k : Type} [Field k] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution [IsAlgClosed k] [Fintype J] [IsIntegral X] (p : X ⟶ Sp k) (hH : H.IsLB) {J₀ : Set J}
    (him : ImmBy p H s J₀) (i : J) (haff : IsAffineOpen (Out.nonzeroLocus (s i)))
    (hne : ((Out.nonzeroLocus (s i) : X.Opens) : Set X).Nonempty)
    (r : J → Γ(X, Out.nonzeroLocus (s i))) (hr : ∀ j, IsRatio (s j) (s i) _ (r j))
    (hc : Subring.closure (Set.range (constFn p (Out.nonzeroLocus (s i))) ∪ Set.range r) = ⊤) :
    MvPolynomial.vanishingIdeal k (cone p H s) = RingHom.ker (coneHom (constHom p _) r) := by
  ext f
  rw [MvPolynomial.mem_vanishingIdeal_iff, RingHom.mem_ker]
  constructor
  · intro hf
    letI : Algebra k Γ(X, Out.nonzeroLocus (s i)) := (constHom p _).toAlgebra
    haveI := finiteType_of_closure (k := k) r hc
    ext n
    refine eq_zero_of_forall_algHom (k := k) _ fun e => ?_
    obtain ⟨x, h, hx, hxe⟩ := exists_point p haff e.toRingHom e.commutes
    obtain ⟨v, hv⟩ := crd_exists hH s x
    obtain ⟨u, hu⟩ := (crd_isUnit_iff i hv).2 h
    have : Polynomial.map e.toRingHom (coneHom (constHom p _) r f) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine ((Set.finite_singleton (0 : k)).infinite_compl).mono fun t ht' => ?_
      have ht : t ≠ 0 := ht'
      have h1 := hf _ ⟨x, hx, crd_smul (Units.mk0 t ht * u⁻¹) hv⟩
      rw [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_map, eval₂_coneHom, ← hxe,
        valHom_comp_constHom p x hx, ← h1]
      have : (fun j => valHom x _ h (r j) * t) = fun j => ((Units.mk0 t ht * u⁻¹ : kˣ) : k) * v j := by
        funext j
        rw [crd_ratio hv (hr j) h, valR_eq x _ h, ← hu, Units.val_mul, Units.val_mk0]
        linear_combination (-(valHom x _ h (r j) * t)) * u.inv_mul
      rw [this]
      rfl
    exact (Polynomial.coeff_map e.toRingHom n).symm.trans (by rw [this]; rfl)
  · rintro hf v ⟨x, hx, hv⟩
    obtain ⟨K, _, y, hy⟩ := exists_generic (X := X)
    obtain ⟨w, hw⟩ := crd_exists hH s y
    have : x (IsLocalRing.closedPoint k) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by rw [him.1]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at this
    obtain ⟨i', hi', hm⟩ := this
    obtain ⟨-, r', hr', -⟩ := him.2 i' hi'
    have h0 := (coneHom_eq_zero_iff p y hy hw i' (hy _ ⟨_, hm⟩) r' hr' f).2
      ((coneHom_eq_zero_iff p y hy hw i (hy _ hne) r hr f).1 hf)
    have h := (top_le_iff x _).2 hm
    have h1 := eval₂_coneHom (constHom p _) r' (valHom x _ h) (v i') f
    rw [h0, Polynomial.eval₂_zero, valHom_comp_constHom p x hx] at h1
    have e2 : v = fun j => valHom x _ h (r' j) * v i' :=
      funext fun j => by rw [← valR_eq]; exact crd_ratio hv (hr' j) h
    rw [← e2] at h1
    exact h1.symm
end GlobalTheory.ZH.ConePrime
