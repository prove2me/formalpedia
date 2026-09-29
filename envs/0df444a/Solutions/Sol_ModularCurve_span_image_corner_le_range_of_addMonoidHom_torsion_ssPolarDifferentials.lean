-- Prove2me | solution 1 for ModularCurve.span_image_corner_le_range_of_addMonoidHom_torsion_ssPolarDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/239a308e-9740-506e-a16d-e219519bbe8e

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_span_image_corner_le_range_of_addMonoidHom_torsion_ssPolarDifferentials

set_option autoImplicit false

namespace T4eAux

open TateModule

variable {p : ℕ} [Fact p.Prime] {Mg : Type} [AddCommGroup Mg]
  {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p Mg)] [IsScalarTower ℤ_[p] 𝕋 (TateModule p Mg)]

omit [Fact p.Prime] in
theorem proj_one_mem (z : TateModule p Mg) : (p : ℤ) • proj p Mg 1 z = 0 := by
  have := torsionBy_proj 1 z
  rwa [pow_one] at this

theorem ringHom_algebraMap_apply {K : Type*} [Field K] [Algebra (ZMod p) K] {V : Type*} [AddCommGroup V] [Module K V]
    (τ : 𝕋 →+* Module.End K V) (c : ℤ_[p]) (ω : V) :
    τ (algebraMap ℤ_[p] 𝕋 c) ω = ((c.appr 1 : ℕ) : ℤ) • ω := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec 1 c)
  have hc : c = (c.appr 1 : ℤ_[p]) + (p : ℤ_[p]) * d := by rw [pow_one] at hd; linear_combination hd
  have hp : (p : Module.End K V) = 0 := by
    ext v
    change (p : Module.End K V) v = 0
    rw [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul K, show ((p : ℕ) : K) = 0 from by
      rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_self, map_zero], zero_smul]
  conv_lhs => rw [hc]
  rw [map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, map_natCast, map_natCast, hp, zero_mul,
    add_zero, Module.End.natCast_apply, natCast_zsmul]

variable (A : AddSubgroup Mg) (hA : ∀ v : Mg, v ∈ A ↔ (p : ℤ) • v = 0)
  {G : Type} (f : G → (Mg →+ Mg)) (op : G → 𝕋)
  (hop : ∀ (g : G) (x : TateModule p Mg) (n : ℕ), ((op g • x : TateModule p Mg) : ℕ → Mg) n = f g ((x : ℕ → Mg) n))
  {K : Type*} [Field K] [Algebra (ZMod p) K] {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} (ι : V → W) (hι : Function.Injective ι) (F : G → V → W)
  (τ : 𝕋 →+* Module.End K V) (hτ : ∀ (g : G) (ω : V), ι (τ (op g) ω) = F g ω)
  (Θ : ↥A →+ V) (hΘ : ∀ (g : G) (x y : ↥A), (y : Mg) = f g (x : Mg) → ι (Θ y) = F g (Θ x))

def lv (z : TateModule p Mg) : ↥A := ⟨proj p Mg 1 z, (hA _).mpr (proj_one_mem z)⟩

omit [Fact p.Prime] in
@[scoped simp] theorem coe_lv (z : TateModule p Mg) : (lv A hA z : Mg) = proj p Mg 1 z := rfl

include hop hι hτ hΘ in

theorem apply_lv_aeval_smul (P : MvPolynomial G ℤ_[p]) :
    ∀ z : TateModule p Mg, Θ (lv A hA (MvPolynomial.aeval op P • z)) = τ (MvPolynomial.aeval op P) (Θ (lv A hA z)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro z
    rw [MvPolynomial.algHom_C, ringHom_algebraMap_apply, ← map_zsmul]
    congr 1
    apply Subtype.ext
    rw [coe_lv, AddSubgroupClass.coe_zsmul, coe_lv, algebraMap_smul, proj_apply, TateModule.smul_apply, proj_apply]
  | add P Q hP hQ =>
    intro z
    rw [map_add, add_smul, map_add, LinearMap.add_apply, ← hP, ← hQ, ← map_add]
    congr 1
  | mul_X P g hP =>
    intro z
    rw [map_mul, MvPolynomial.aeval_X, map_mul, Module.End.mul_apply, mul_smul, hP]
    congr 1
    apply hι
    rw [hτ]
    apply hΘ
    rw [coe_lv, coe_lv, proj_apply, proj_apply, hop]

include hA hop hι hτ hΘ in

theorem main (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (e : 𝕋) :
    Submodule.span K (Θ '' {x : ↥A | (x : Mg) ∈
        ((IharaLemma.cornerSubmodule (M := TateModule p Mg) e).toAddSubgroup).map (TateModule.proj p Mg 1)}) ≤
      LinearMap.range (τ e) := by
  obtain ⟨P, rfl⟩ : ∃ P : MvPolynomial G ℤ_[p], MvPolynomial.aeval op P = e := by
    have : e ∈ (MvPolynomial.aeval (R := ℤ_[p]) op).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]; exact Algebra.mem_top
    exact this
  rw [Submodule.span_le]
  rintro w ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨z, rfl⟩ : ∃ z, MvPolynomial.aeval op P • z = y := by
    obtain ⟨z, hz⟩ := (hy : y ∈ IharaLemma.cornerSubmodule (M := TateModule p Mg) (MvPolynomial.aeval op P))
    exact ⟨z, hz⟩
  have hxz : x = lv A hA (MvPolynomial.aeval op P • z) := Subtype.ext hyx.symm
  rw [SetLike.mem_coe, hxz, apply_lv_aeval_smul A hA f op hop ι hι F τ hτ Θ hΘ P z]
  exact LinearMap.mem_range_self _ _

end T4eAux
p2m_reactivate "P2MW.S_ModularCurve_span_image_corner_le_range_of_addMonoidHom_torsion_ssPolarDifferentials.T4eAux"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (τ : 𝕋 →+* Module.End K
      (ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hτ : ∀ (g : CohCarrier.Gen M S)
      (ω : ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),
      ((τ (op g) ω : ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ModularCurve.genDiffModL K p M H hpM S g ω)

    (Θ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) →+ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)
    (hΘhecke : ∀ (g : CohCarrier.Gen M S) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (y : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
          ((Θ y : ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
            Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ModularCurve.genDiffModL K p M H hpM S g (Θ x))
    :
    Submodule.span K (Θ '' {x | (x : ModularCurve.JH M H) ∈
          ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1)}) ≤ LinearMap.range (τ (S'.e i₀)) := by
  exact T4eAux.main (p := p) (Mg := ModularCurve.JH M H)
    (V := ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)
    (fun v => AlgebraicCurve.Pic0.mem_torsion) (ModularCurve.genOpH M H S) op
    (fun g x n => by rw [hop, ModularCurve.tateGenOpH_apply_coe])
    Subtype.val Subtype.val_injective
    (fun g ω => ModularCurve.genDiffModL K p M H hpM S g ω) τ hτ Θ hΘhecke hgen (S'.e i₀)

end S_ModularCurve_span_image_corner_le_range_of_addMonoidHom_torsion_ssPolarDifferentials
end P2MW
export P2MW.S_ModularCurve_span_image_corner_le_range_of_addMonoidHom_torsion_ssPolarDifferentials (solution)
