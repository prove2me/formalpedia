-- Prove2me | solution 1 for GlobalTheory.TateMatrices.tangent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:44:53.169675+00:00
-- url     : https://prove2.me/submissions/417d6399-6d18-4727-b4a7-d0e9cb6b3abd

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀)
namespace GlobalTheory.TateMatrices
theorem _root_.solution {O R : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg) (f : OEnd B O)
    (M : Matrix (Fin g) (Fin g) (O : Type)) (s : LHom O R) (Dp : DualPair R)
    (hM : ∀ (l : Fin g) (i : Dp.π.ker) (m : Fin g → Dp.π.ker),
      (∀ k, (m k : (Dp.D : Type)) = (Dp.σ.comp s).1 (M k l) * i) →
      f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] i)) =
        B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] m k)) (v : B.gg) :
    f.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap
        (gb.constr R₀ (fun l => ∑ k, gb k ⊗ₜ[R₀] s.1 (M k l)) v)) := by
  rw [← gb.sum_repr v, TensorProduct.sum_tmul, map_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.smul_tmul, map_smul, Module.Basis.constr_basis, map_smul, map_sum,
    Finset.smul_sum,
    hM l _ (fun k => gb.repr v l • Dp.ηmap (s.1 (M k l))) (fun k => by
      simp only [DualPair.ηmap, DualPair.ηk, LHom.comp, LinearMap.coe_mk, AddHom.coe_mk,
        SetLike.val_smul, AlgHom.comp_apply, mul_smul_comm])]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.lTensor_tmul, TensorProduct.tmul_smul]
end GlobalTheory.TateMatrices
