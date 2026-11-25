-- Prove2me | solution 1 for GlobalTheory.reducedWigner_lowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:12.392652+00:00
-- url     : https://prove2.me/submissions/fb8cf4e3-8ca9-4849-bece-87de7fc614ee

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LastComatrixRowInvertsDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenvalueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorDualStandardRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReducedWignerCoefficientLowering
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp
import Theorems.Thm_GlobalTheory_ev_starProjection_eigenspace_eq_residue
import Theorems.Thm_GlobalTheory_lastComatrixRow_inverts_dual
import Theorems.Thm_GlobalTheory_splitCasimir_eigenvalue_dual
import Theorems.Thm_GlobalTheory_tensor_dual_standard_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hE hEt hOm M v hv
  set m : Fin (n + 1) → ℂ := shf β L with hm
  have hcap : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v := fun w v => hH.cap w v
  have hrel := tensor_dual_standard_rel V n E Et Om hH.gl hE hEt hOm
  obtain ⟨K, hK1, hK2⟩ := lastComatrixRow_inverts_dual V n E Om m hH.gl hcap hOm
  have hinj : Function.Injective m := by
    intro i j hij
    have h1 : ((L i : ℤ) : ℂ) = ((L j : ℤ) : ℂ) := by
      simpa [hm, shf] using hij
    exact hH.anti.injective (by exact_mod_cast h1)
  let ev : PiLp 2 (fun _ : Fin (n + 1) => V) →ₗ[ℂ] V :=
    { toFun := fun x => x (Fin.last n)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let q : ℂ → ℂ := fun u => ∏ j, (u + shf β M j)
  have hq : Continuous q := by
    exact continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)
  have hKy : ∀ u, K u (PiLp.single 2 (Fin.last n) v) = q u • v := by
    intro u
    rw [hK2]
    exact (mem_CapSp.mp hv) u
  have hres := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    m (n : ℂ) Om ev K q (PiLp.single 2 (Fin.last n) v) v l hinj hrel.2.2.1
    (splitCasimir_eigenvalue_dual V n E Et Om m hH.gl hE hcap hEt hOm)
    (fun u x => hK1 u x) hq hKy
  have hev : m l + (n : ℂ) = β + L l + (n : ℂ) := by simp [hm, shf]
  rw [hev] at hres
  change ev _ = _
  rw [hres]
  congr 1
  simp only [q, hm, shf, WigSh.wM]
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    ring
  · apply Finset.prod_congr rfl
    intro j _
    ring
end GlobalTheory
