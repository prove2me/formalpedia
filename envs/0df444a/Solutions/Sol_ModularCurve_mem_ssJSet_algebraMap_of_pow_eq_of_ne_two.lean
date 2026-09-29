-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b386f4c2-a4dc-5ef6-90fd-1aefed976f95

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet mem_ssJSet_iff"
p2m_open "ModularCurve"
namespace TransGen

open WeierstrassCurve WeierstrassCurve.Affine

section transport
variable {F : Type*} {L : Type*} [Field F] [Field L] (f : F →+* L) {W₀ : WeierstrassCurve F}

theorem some_congr {V : Affine L} {x₁ y₁ x₂ y₂ : L} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def pmap : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

@[scoped simp] lemma pmap_zero : pmap f (0 : W₀.toAffine.Point) = 0 := rfl

lemma pmap_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    pmap f (.some x y h) = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

lemma pmap_injective : Function.Injective (pmap f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [pmap_some, pmap_some, Affine.Point.some.injEq] at h
    exact some_congr (f.injective h.1) (f.injective h.2) _ _

theorem pmap_add [DecidableEq F] [DecidableEq L] (P Q : W₀.toAffine.Point) :
    pmap f (P + Q) = pmap f P + pmap f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, pmap_zero, pmap_some, pmap_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, pmap_some, pmap_some, pmap_some, Affine.Point.add_some hxy']
    exact some_congr (by rw [Affine.map_slope, Affine.map_addX]) (by rw [Affine.map_slope, Affine.map_addY]) _ _

def phom [DecidableEq F] [DecidableEq L] : W₀.toAffine.Point →+ (W₀.map f).toAffine.Point :=
  AddMonoidHom.mk' (pmap f) (pmap_add f)

@[scoped simp] lemma phom_apply [DecidableEq F] [DecidableEq L] (P : W₀.toAffine.Point) : phom f P = pmap f P := rfl

end transport

theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : ℕ) (W : WeierstrassCurve R) :
    (W.map f).hasseInvariant q = f (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  have : (W.map f).twoTorsionPolynomial = Cubic.map f W.twoTorsionPolynomial := by
    simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
      WeierstrassCurve.map_b₆, map_ofNat, map_mul]
  rw [this, Cubic.map_toPoly, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem exists_pow_eq_of_isAlgebraic {K : Type*} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] [Algebra (ZMod q) K]
    (x : K) (hx : IsAlgebraic (ZMod q) x) : ∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x := by
  classical
  have hint : IsIntegral (ZMod q) x := hx.isIntegral
  haveI : FiniteDimensional (ZMod q) (IntermediateField.adjoin (ZMod q) {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod q) {x}) := Module.finite_of_finite (ZMod q)
  letI : Fintype (IntermediateField.adjoin (ZMod q) {x}) := Fintype.ofFinite _
  haveI : CharP (IntermediateField.adjoin (ZMod q) {x}) q :=
    charP_of_injective_algebraMap (algebraMap (ZMod q) (IntermediateField.adjoin (ZMod q) {x})).injective q
  obtain ⟨n, -, hcard⟩ := FiniteField.card (IntermediateField.adjoin (ZMod q) {x}) q
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : IntermediateField.adjoin (ZMod q) {x})
  rw [hcard] at h
  exact congrArg (fun y : IntermediateField.adjoin (ZMod q) {x} => (y : K)) h

end TransGen
p2m_reactivate "P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.ModularCurve.TransGen"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.ModularCurve.TransGen P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.ModularCurve ModularCurve.TransGen in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {k K : Type*} [Field k] [Field K] [CharP k q] [CharP K q] [DecidableEq k] [DecidableEq K]
    [Algebra k K] [IsAlgClosed K]
    (hk : ∀ x : K, (∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x) → x ∈ (algebraMap k K).range)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) :
    algebraMap k K a ∈ ssJSet q K := by
  classical
  set ι := algebraMap k K with hι
  letI : Algebra (ZMod q) K := ZMod.algebra K q
  let K₀ : IntermediateField (ZMod q) K := algebraicClosure (ZMod q) K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed (ZMod q)
  haveI : CharP K₀ q := charP_of_injective_algebraMap (algebraMap (ZMod q) K₀).injective q

  have halg : ∀ x : K₀, IsAlgebraic (ZMod q) (x : K) := fun x => mem_algebraicClosure_iff.mp x.2
  have hk' : ∀ x : K₀, ∃ y : k, ι y = x := fun x => by
    obtain ⟨n, hn, hx⟩ := exists_pow_eq_of_isAlgebraic q (x : K) (halg x)
    obtain ⟨y, hy⟩ := hk (x : K) ⟨n, hn, hx⟩
    exact ⟨y, hy⟩
  choose τf hτf using hk'
  have hτinj : ∀ x y : K₀, τf x = τf y → x = y := fun x y h =>
    Subtype.ext (by rw [← hτf x, ← hτf y, h])
  let τ : K₀ →+* k :=
    { toFun := τf
      map_one' := ι.injective (by rw [hτf, map_one]; rfl)
      map_mul' := fun x y => ι.injective (by rw [hτf, map_mul, hτf, hτf]; rfl)
      map_zero' := ι.injective (by rw [hτf, map_zero]; rfl)
      map_add' := fun x y => ι.injective (by rw [hτf, map_add, hτf, hτf]; rfl) }
  have hτ : ∀ x : K₀, ι (τ x) = x := hτf

  have haK : IsAlgebraic (ZMod q) (ι a) := by
    refine ⟨Polynomial.X ^ (q ^ 2) - Polynomial.X, ?_, ?_⟩
    · apply Polynomial.Monic.ne_zero
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt
      exact_mod_cast this
    · rw [map_sub, map_pow, Polynomial.aeval_X, ← map_pow, ha2, sub_self]
  let a₀ : K₀ := ⟨ι a, mem_algebraicClosure_iff.mpr haK⟩
  have hτa : τ a₀ = a := ι.injective (hτ a₀)

  let W₀ : WeierstrassCurve K₀ := WeierstrassCurve.ofJ a₀
  have hW₀ : ∀ P : W₀.toAffine.Point, q • P = 0 → P = 0 := by
    intro P hP
    have hj : (W₀.map τ).j = a := by rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j, hτa]
    have h := (mem_ssJSet_iff.mp ha) (W₀.map τ) hj (phom τ P) (by rw [← map_nsmul, hP, map_zero])
    rw [phom_apply] at h
    exact pmap_injective τ (h.trans (pmap_zero τ).symm)
  have hH0 : W₀.hasseInvariant q = 0 :=
    (WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq2 W₀).mp hW₀

  rw [mem_ssJSet_iff]
  intro W' _ hj' P hP
  let W₁ : WeierstrassCurve K := W₀.map (algebraMap K₀ K)
  have hW₁j : W₁.j = ι a := by
    rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j]; rfl
  have hH1 : W₁.hasseInvariant q = 0 := by rw [hasseInvariant_map, hH0, map_zero]
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W₁ W' (hW₁j.trans hj'.symm)
  have hH' : W'.hasseInvariant q = 0 := by
    rw [← hC, WeierstrassCurve.hasseInvariant_variableChange, hH1, mul_zero]
  exact ((WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq2 W').mpr hH') P hP

end S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two (solution)
