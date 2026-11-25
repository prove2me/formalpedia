-- Prove2me | solution 1 for GlobalTheory.MomOne.Mdl.exists_pointHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:49.396311+00:00
-- url     : https://prove2.me/submissions/d08ec481-9848-47ea-9216-4cd7d788422c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_RingHomPointBijective
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint
attribute [local simp] GlobalTheory.latticePointEquiv_mk


section
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical
noncomputable section
namespace GlobalTheory.MomOne
open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_some {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W (.some x y h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl
open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_surjective_of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (_root_.GlobalTheory.MomOne.ringHomPoint (e : k →+* k') W) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · have h' : W.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (e : k →+* k')) e.injective]
      simpa using h
    refine ⟨.some _ _ h', ?_⟩
    rw [ringHomPoint_some]
    simp
open PowerSeries WeierstrassCurve WeierstrassCurve.Affine in
open scoped ComplexConjugate BigOperators Topology in
open Classical in
private lemma ringHomPoint_eq_zero_iff {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [ringHomPoint_some]
    simp
end GlobalTheory.MomOne
end
end

set_option autoImplicit false
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MomOne
open PowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical
namespace GlobalTheory.MomOne
namespace _root_.GlobalTheory.MomOne.Mdl
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by
  obtain ⟨hc, -, -, -, -, -, -, h₄, h₆⟩ := hM
  have hιc : M.ι M.c ≠ 0 :=
    (map_ne_zero M.ι).mpr hc
  obtain ⟨C, hCu, hCr, hCs, hCt⟩ : ∃ C : VariableChange ℂ_[q],
      (C.u : ℂ_[q]) = (M.ι M.c)⁻¹ ∧
      C.r = -(M.W.b₂ / 12) ∧ C.s = -(M.W.a₁ / 2) ∧
      C.t = M.W.a₁ * M.W.b₂ / 24 -
        M.W.a₃ / 2 :=
    ⟨⟨Units.mk0 _ (inv_ne_zero hιc), _, _, _⟩, rfl, rfl, rfl, rfl⟩
  have hCu' : ((C.u⁻¹ : ℂ_[q]ˣ) : ℂ_[q]) = M.ι M.c := by
    rw [Units.val_inv_eq_inv_val, hCu, inv_inv]
  have hE : (_root_.GlobalTheory.latticeCurve M.L).a₁ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₂ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₃ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₄ = -M.L.g₂ / 4 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₆ = -M.L.g₃ / 4 := by
    simp [_root_.GlobalTheory.latticeCurve]
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := hE
  have hg₂ : M.ι M.L.g₂ =
      M.W.c₄ / 12 * M.ι M.c ^ 4 := by
    rw [h₄, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hιc)]
  have hg₃ : M.ι M.L.g₃ =
      M.W.c₆ / 216 * M.ι M.c ^ 6 := by
    rw [h₆, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 6 hιc)]
  have hC : C • M.W =
      (_root_.GlobalTheory.latticeCurve M.L).map (M.ι : ℂ →+* ℂ_[q]) := by
    ext
    · rw [variableChange_a₁, hCu', hCs, map_a₁, hE₁]; simp only [map_zero]; ring
    · rw [variableChange_a₂, hCu', hCs, hCr, map_a₂, hE₂]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₃, hCu', hCt, hCr, map_a₃, hE₃]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₄, hCu', hCs, hCt, hCr, map_a₄, hE₄]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₂, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    · rw [variableChange_a₆, hCu', hCt, hCr, map_a₆, hE₆]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₃, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      ring
  let φ : ℂ →+ M.W.toAffine.Point :=
    (_root_.GlobalTheory.variableChangePoint C hC).comp
      ((_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)).comp
        (_root_.GlobalTheory.latticePointHom M.L))
  have hφ : ∀ z, φ z = _root_.GlobalTheory.variableChangePoint C hC
      (_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)
        (_root_.GlobalTheory.latticePoint M.L z)) := by
    intro z
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, _root_.GlobalTheory.latticePointHom_apply]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨P₁, rfl⟩ := (_root_.GlobalTheory.variableChangePoint_bijective C hC).2 P
    obtain ⟨P₂, rfl⟩ := ringHomPoint_surjective_of_ringEquiv M.ι _ P₁
    obtain ⟨z, rfl⟩ := _root_.GlobalTheory.latticePoint_surjective M.L P₂
    exact ⟨z, hφ z⟩
  · intro z
    rw [hφ, map_eq_zero_iff _ (_root_.GlobalTheory.variableChangePoint_bijective C hC).1,
      ringHomPoint_eq_zero_iff, _root_.GlobalTheory.latticePoint_eq_zero_iff]
  · intro z hz
    have key : ∀ {a b a' b' : ℂ_[q]} (h : M.W.toAffine.Nonsingular a b),
        a = a' → b = b' → ∃ h', (Point.some a b h : M.W.toAffine.Point) =
          Point.some a' b' h' := by
      rintro a b a' b' h rfl rfl
      exact ⟨h, rfl⟩
    have hx : (C.u : ℂ_[q]) ^ 2 * M.ι (M.L.weierstrassP z) + C.r =
        M.ι (M.x z) := by
      show _ = M.ι (M.L.weierstrassP z / M.c ^ 2 -
        M.ι.symm (M.W.b₂ / 12))
      rw [map_sub, map_div₀, map_pow, RingEquiv.apply_symm_apply, hCu, hCr]
      field_simp
      ring
    have hy : (C.u : ℂ_[q]) ^ 3 * M.ι (M.L.derivWeierstrassP z / 2) +
        (C.u : ℂ_[q]) ^ 2 * C.s * M.ι (M.L.weierstrassP z) + C.t =
        M.ι (M.y z) := by
      show _ = M.ι ((M.L.derivWeierstrassP z /
        M.c ^ 3 - M.ι.symm M.W.a₁ *
        M.x z - M.ι.symm M.W.a₃) / 2)
      simp only [map_div₀, map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
      rw [← hx, hCu, hCr, hCs, hCt]
      field_simp
      ring
    rw [hφ, _root_.GlobalTheory.latticePoint_of_notMem M.L hz,
      ringHomPoint_some, _root_.GlobalTheory.variableChangePoint_some]
    exact key _ hx hy
end _root_.GlobalTheory.MomOne.Mdl
end GlobalTheory.MomOne
