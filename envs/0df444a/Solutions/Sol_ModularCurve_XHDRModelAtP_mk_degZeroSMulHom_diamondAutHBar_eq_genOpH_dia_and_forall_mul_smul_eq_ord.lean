-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2ff5fdb4-80e8-598d-ba71-05962cb54897

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

namespace Ws49
namespace CDivDia

theorem exists_point_comp_eq
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔛 : XHDRModelAtP p M H hpM hj) (g : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj) (hg : g ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g := by
  haveI := 𝔛.eeta_iso
  have hcond : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, Category.assoc, Category.assoc, hg, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
      ← Category.assoc, y.2]
  let q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :=
    pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g) (𝟙 _) hcond
  refine ⟨⟨q ≫ inv 𝔛.eeta, ?_⟩, ?_⟩
  · rw [Category.assoc, ← 𝔛.heeta, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  · show (q ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

theorem wgen_smul_dia_smul
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)
    (e : (ZMod M)ˣ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    wgen • (SemilinearAut.ofAlgAut (diamondAutHBar M H e) • V) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H e) • (wgen • V) := by
  obtain ⟨y₀, rfl⟩ := 𝔛.Meta.pointEquivPlace.surjective V
  have hwinv : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]

  obtain ⟨y₁, hy₁⟩ := exists_point_comp_eq 𝔛 (𝔛.dia e).hom (𝔛.dia_over e) y₀
  have h₁ : 𝔛.Meta.pointEquivPlace y₁ = SemilinearAut.ofAlgAut (diamondAutHBar M H e) • 𝔛.Meta.pointEquivPlace y₀ :=
    𝔛.dia_generic e y₀ y₁ hy₁

  obtain ⟨y₂, hy₂⟩ := exists_point_comp_eq 𝔛 𝔛.w.inv hwinv y₁
  obtain ⟨y₃, hy₃⟩ := exists_point_comp_eq 𝔛 𝔛.w.inv hwinv y₀
  have h₂ : 𝔛.Meta.pointEquivPlace y₂ = wgen • 𝔛.Meta.pointEquivPlace y₁ := by
    apply hwgen y₁ y₂
    rw [reassoc_of% hy₂]
    simp only [Iso.inv_hom_id, Category.comp_id]
  have h₃ : 𝔛.Meta.pointEquivPlace y₃ = wgen • 𝔛.Meta.pointEquivPlace y₀ := by
    apply hwgen y₀ y₃
    rw [reassoc_of% hy₃]
    simp only [Iso.inv_hom_id, Category.comp_id]

  have hcomm : (𝔛.dia e).hom ≫ 𝔛.w.inv = 𝔛.w.inv ≫ (𝔛.dia e).hom := by
    rw [Iso.comp_inv_eq, Category.assoc, ← 𝔛.w_dia e, Iso.inv_hom_id_assoc]

  have h₄ : 𝔛.Meta.pointEquivPlace y₂ = SemilinearAut.ofAlgAut (diamondAutHBar M H e) • 𝔛.Meta.pointEquivPlace y₃ := by
    apply 𝔛.dia_generic e y₃ y₂
    rw [hy₂, reassoc_of% hy₁, hcomm, reassoc_of% hy₃]
  rw [← h₁, ← h₂, h₄, h₃]

end Ws49.CDivDia

open Ws49.CDivDia in
open ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)
    (e : (ZMod M)ˣ)
    (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (hDf : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) :
    (AlgebraicCurve.Pic0.mk (SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D) : ModularCurve.JH M H) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.dia e) (AlgebraicCurve.Pic0.mk D) ∧
    ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • ((SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D :
          AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) :
            AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v =
        v.ord (diamondAutHBar M H e f) := by
  set σ : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
    SemilinearAut.ofAlgAut (diamondAutHBar M H e) with hσ
  refine ⟨?_, fun v => ?_⟩
  · rw [ModularCurve.genOpH_dia, ModularCurve.diamondHBar_apply, SemilinearAut.pic0_smul_mk]
  ·
    have hcoe : ((SemilinearAut.degZeroSMulHom σ D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(ModularCurve.xHFunctionFieldBar M H))) : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
        σ • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) :=
      SemilinearAut.coe_degZeroSMulHom σ D
    have hsw : wgen • (σ • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) =
        σ • (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) := by
      simp only [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_comp.symm]
      congr 1
      funext V
      exact wgen_smul_dia_smul 𝔛 wgen hwgen e V
    rw [hcoe, hsw, SemilinearAut.divisor_smul_apply, hDf (σ⁻¹ • v)]
    have h := SemilinearAut.ord_smul σ (σ⁻¹ • v) f
    rw [smul_inv_smul] at h

    exact h.symm

end S_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord (solution)
