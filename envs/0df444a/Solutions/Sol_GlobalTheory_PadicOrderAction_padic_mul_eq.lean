-- Prove2me | solution 1 for GlobalTheory.PadicOrderAction.padic_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:25.047981+00:00
-- url     : https://prove2.me/submissions/3e587d8c-b921-470c-ba51-14dcecaa79a2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PadicOrderAction
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.PadicOrderAction
theorem _root_.solution {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by
  have h : c - ((PadicInt.toZMod c).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = d * p + ((PadicInt.toZMod c).val : ℤ_[p]) := by rw [hd]; ring
  rw [nsmul_eq_mul] at hi ⊢
  conv_lhs => rw [hc]
  rw [map_add, map_mul, map_natCast, map_natCast, add_mul, _root_.mul_assoc, hi, mul_zero, zero_add]
end GlobalTheory.PadicOrderAction
