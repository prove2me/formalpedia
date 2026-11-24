-- Prove2me | solution 1 for GlobalTheory.DerLin.isCombAt_iff_isDerivAt0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:41.720837+00:00
-- url     : https://prove2.me/submissions/53dba56e-7ab5-4a32-889e-dca8d31b354c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
import Theorems.Thm_GlobalTheory_DerLin_le_of_fst_eq
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_T_derivative_along_tangent_combination_moduli
import Theorems.Thm_GlobalTheory_T_exists_tangent_module_universal_group
import Theorems.Thm_GlobalTheory_T_exponential_derivative_at_zero_isTangent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.DerLin
namespace GlobalTheory.DerLin
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (w : Fin m → (Fin g → ℂ)), (∀ i, IsDerivAt0 (fun z => (F.ex k P z).left) (w i) (v i)) → ∀ (a : Fin m → ℂ) (v' : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsCombAt (F.u k P) v a v' ↔ IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP m v w hvw a
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.exponential_derivative_at_zero_isTangent E H Dw l Xo σ' g ty F k P hP
  obtain ⟨N, _, _, ν, ρ, -, hr, hc, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo ℂ (F.u k P)
  have htan : ∀ i, IsTanAt (F.u k P) (v i) := fun i => h1 _ _ (hvw i)
  choose b hb using fun i => (hr (v i)).1 (htan i)
  have hv : v = fun i => ν (b i) := funext fun i => (hb i).symm
  have fwd : ∀ v', IsCombAt (F.u k P) v a v' →
      IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
    intro v' hv'
    have ht' : IsTanAt (F.u k P) v' := by
      rw [hv, hc] at hv'
      exact (hr v').2 ⟨_, hv'.symm⟩
    obtain ⟨v0, hv0, -⟩ := h2 0
    refine ⟨ht'.2.trans ((h1 _ _ hv0).2.symm.trans hv0.1), fun U h f => ?_⟩
    have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => le_of_fst_eq ((htan i).2.trans ht'.2.symm) h
    refine (GlobalTheory.T.derivative_along_tangent_combination_moduli E H Dw l Xo ℂ (F.u k P) m v a v' htan hv' U h hU f).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (a i * ·) ((hvw i).2 U (hU i) f)
  intro v'
  refine ⟨fwd v', fun hd => ?_⟩
  have hex : IsCombAt (F.u k P) v a (ν (∑ i, a i • b i)) := by
    rw [hv, hc]
  rw [(h2 _).unique hd (fwd _ hex)]
  exact hex
end GlobalTheory.DerLin
