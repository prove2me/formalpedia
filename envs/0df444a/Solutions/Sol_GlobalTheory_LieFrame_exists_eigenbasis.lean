-- Prove2me | solution 1 for GlobalTheory.LieFrame.exists_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:39.538941+00:00
-- url     : https://prove2.me/submissions/ea78eaba-c4e0-4d1c-b436-592e5a9bb2ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsEigAtIffOfIsDerivAt0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentEigenbasisExponential
import Theorems.Thm_GlobalTheory_LieFrame_sum_single_apply
import Theorems.Thm_GlobalTheory_LieFrame_eq_sum_single
import Theorems.Thm_GlobalTheory_DerLin_isCombAt_iff_isDerivAt0
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_isDerivAt0_ex_isTanAt
import Theorems.Thm_GlobalTheory_isEigAt_iff_of_isDerivAt0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.LieFrame
namespace GlobalTheory.LieFrame
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v := fun τ i => (h2 _).exists
  choose u hu using hu
  refine ⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩
  · refine (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_
    by_cases hji : j = e.symm ⟨τ, i⟩
    · subst hji
      simp
    · exact absurd (Pi.single_eq_of_ne hji _) hj
  · obtain ⟨z, hz, huniq⟩ := h3 w hw
    have hs := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew
    have hc := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)
    refine ⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩
    · rw [eq_sum_single e τ z hs]
      exact hz
    · have h4 := huniq _ ((hc a w).1 ha)
      funext i
      exact (sum_single_apply e τ a i).symm.trans (congrFun h4 _)
end GlobalTheory.LieFrame
