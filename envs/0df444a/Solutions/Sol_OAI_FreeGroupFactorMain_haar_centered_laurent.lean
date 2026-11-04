-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.haar_centered_laurent
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:45:10.087191+00:00
-- url     : https://prove2.me/submissions/82f22241-1c3a-4d98-9a3e-9ca97f3eb214

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

theorem norm_canonicalTrace_le {G : Type uG} [Group G] (T : groupVonNeumann G) :
    ‖canonicalTrace T‖ ≤ ‖T‖ := by
  classical
  rw [canonicalTrace_eq_inner]
  calc
    ‖inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
        ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))‖ ≤
        ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        (‖(T : GroupOperator G)‖ * ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖) := by
      gcongr
      exact (T : GroupOperator G).le_opNorm _
    _ = ‖T‖ := by simp

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

theorem groupVN_matrix {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x y : G) :
    ((T : GroupOperator G) (lp.single 2 y 1)) x =
      ((T : GroupOperator G) deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne)
    (groupVN_commute_right T y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

theorem groupVN_star_coefficient {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x : G) :
    ((star T : GroupOperator G) deltaOne) x =
      conj (((T : GroupOperator G) deltaOne) x⁻¹) := by
  calc
    ((star T : GroupOperator G) deltaOne) x =
        inner ℂ (lp.single 2 x (1 : ℂ)) ((star T : GroupOperator G) deltaOne) := by
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    _ = inner ℂ ((T : GroupOperator G) (lp.single 2 x 1)) deltaOne := by
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj (((T : GroupOperator G) (lp.single 2 x 1)) 1) := by
      simp only [deltaOne, lp.inner_single_right, RCLike.inner_apply, one_mul]
    _ = _ := by rw [groupVN_matrix]; simp

theorem canonicalTrace_star_mul_inner {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) :
    canonicalTrace (star T * U) = inner ℂ
      ((T : GroupOperator G) deltaOne) ((U : GroupOperator G) deltaOne) := by
  classical
  rw [canonicalTrace_eq_inner, ← deltaOne_eq]
  change inner ℂ deltaOne (star (T : GroupOperator G) ((U : GroupOperator G) deltaOne)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

open scoped ComplexConjugate ENNReal

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

theorem twoNorm_le_norm {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm T ≤ ‖T‖ := by
  calc
    _ ≤ ‖(T : GroupOperator G)‖ * ‖(deltaOne : GroupHilbert G)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [deltaOne, lp.norm_single]

theorem canonicalTrace_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTrace (star T) = star (canonicalTrace T) := by
  classical
  have hh := groupVN_star_coefficient T 1
  change ((star T : GroupOperator G) (lp.single 2 1 1)) 1 =
    (starRingEnd ℂ) (((T : GroupOperator G) (lp.single 2 1 1)) 1)
  simpa only [deltaOne_eq, inv_one] using hh

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.MobiusLog
variable {A : Type uA} [CommCStarAlgebra A] [Nontrivial A]

theorem norm_neg_smul_star_lt (C : unitary A) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖-r • star (C : A)‖ < 1 := by
  calc
    ‖-r • star (C : A)‖ = r * ‖(C : A)‖ := by
      rw [norm_smul, norm_star, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr0]
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left (CStarRing.norm_coe_unitary C).le hr0
    _ < 1 := by simpa using hr1

def denominator (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : Aˣ :=
  Units.oneSub (-r • star (C : A)) (norm_neg_smul_star_lt C hr0 hr1)

@[simp] theorem denominator_coe (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (denominator C r hr0 hr1 : A) = 1 + r • star (C : A) := by
  simp [denominator, sub_neg_eq_add]

def mobius (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : unitary A :=
  ⟨((star (denominator C r hr0 hr1)) * (denominator C r hr0 hr1)⁻¹ : Aˣ), by
    apply (Units.mul_inv_mem_unitary _ _).mpr
    rw [star_star, mul_comm]⟩

theorem denominator_add_star_isUnit (C : unitary A) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsUnit ((denominator C r hr0 hr1 : A) + star (denominator C r hr0 hr1 : A)) := by
  have hn : ‖-(r/2) • ((C : A) + star (C : A))‖ < 1 := by
    calc
      _ = (r/2) * ‖(C : A) + star (C : A)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      _ ≤ (r/2) * (1+1) := by
        gcongr
        exact (norm_add_le _ _).trans (by
          rw [norm_star]
          exact add_le_add (CStarRing.norm_coe_unitary C).le (CStarRing.norm_coe_unitary C).le)
      _ < 1 := by linarith
  have hu := isUnit_one_sub_of_norm_lt_one hn
  have he : (denominator C r hr0 hr1 : A) + star (denominator C r hr0 hr1 : A) =
      (2 : ℝ) • (1 - (-(r/2) • ((C : A) + star (C : A)))) := by
    simp only [denominator_coe, star_add, star_one, star_smul, star_trivial, star_star]
    module
  rw [he]
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr (by norm_num) : IsUnit (2 : ℝ)).map
    (algebraMap ℝ A)).mul hu

theorem mobius_add_one_isUnit (C : unitary A) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsUnit ((mobius C r hr0 hr1 : A) + 1) := by
  have hu := denominator_add_star_isUnit C r hr0 hr1
  have he : ((mobius C r hr0 hr1 : A) + 1) * (denominator C r hr0 hr1 : A) =
      (denominator C r hr0 hr1 : A) + star (denominator C r hr0 hr1 : A) := by
    simp only [mobius, Units.val_mul, Units.coe_star, add_mul, mul_assoc,
      Units.inv_mul, mul_one, one_mul]
    exact add_comm _ _
  rw [← he] at hu
  exact (IsUnit.mul_iff.mp hu).1

theorem mobius_norm_sub_one_lt_two (C : unitary A) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖(mobius C r hr0 hr1 : A) - 1‖ < 2 := by
  apply (Unitary.norm_sub_one_lt_two_iff (mobius C r hr0 hr1).property).mpr
  rw [spectrum.notMem_iff]
  simpa [sub_eq_add_neg, add_comm] using
    (mobius_add_one_isUnit C r hr0 hr1).neg

theorem mobius_bounded_log (C : unitary A) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ S : selfAdjoint A, ‖S‖ ≤ Real.pi ∧ selfAdjoint.expUnitary S = mobius C r hr0 hr1 := by
  exact ⟨Unitary.argSelfAdjoint _, Unitary.norm_argSelfAdjoint_le_pi _,
    expUnitary_argSelfAdjoint (mobius_norm_sub_one_lt_two C r hr0 hr1)⟩

theorem mobius_decomp (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (mobius C r hr0 hr1 : A) = r • (C : A) +
      (1-r^2) • ((denominator C r hr0 hr1)⁻¹ : Aˣ) := by
  let q := denominator C r hr0 hr1
  have he : (r • (C : A) + (1-r^2) • ((q⁻¹ : Aˣ) : A)) * (q : A) = star (q : A) := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, Units.inv_mul, denominator_coe,
      mul_add, mul_one, mul_smul_comm, C.property.2]
    simp only [star_add, star_one, star_smul, star_trivial, star_star, smul_add, smul_smul]
    module
  have hh := congrArg (fun x : A => x * ((q⁻¹ : Aˣ) : A)) he
  simpa only [mul_assoc, Units.mul_inv, mul_one, mobius, Units.val_mul, Units.coe_star]
    using hh.symm

theorem trace_star_mul_denominator_inv (C : unitary A) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ m : ℤ, τ ((C^m : unitary A) : A) = if m = 0 then 1 else 0)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    τ (star (C : A) * ((denominator C r hr0 hr1)⁻¹ : Aˣ)) = 0 := by
  let t : A := -r • star (C : A)
  have hs := summable_geometric_of_norm_lt_one (norm_neg_smul_star_lt C hr0 hr1)
  change τ (star (C : A) * ∑' m : ℕ, t^m) = _
  rw [← hs.tsum_mul_left, τ.map_tsum (hs.mul_left _)]
  have hz : ∀ m : ℕ, τ (star (C : A) * t^m) = 0 := by
    intro m
    have he : star (C : A) * (star (C : A))^m = ((C^(-(m+1 : ℤ)) : unitary A) : A) := by
      rw [show (m:ℤ)+1 = ((m+1:ℕ):ℤ) by simp, zpow_neg, zpow_natCast,
        ← Unitary.star_eq_inv]
      rw [Unitary.coe_star, SubmonoidClass.coe_pow, star_pow, pow_succ']
    dsimp [t]
    rw [smul_pow, mul_smul_comm, he, τ.map_smul_of_tower]
    rw [hτ, ite_eq_right (by omega), smul_zero]
  change (∑' m : ℕ, τ (star (C : A) * t^m)) = 0
  simp only [hz, tsum_zero]

theorem trace_star_mul_mobius (C : unitary A) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ m : ℤ, τ ((C^m : unitary A) : A) = if m = 0 then 1 else 0)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    τ (star (C : A) * (mobius C r hr0 hr1 : A)) = (r : ℂ) := by
  rw [mobius_decomp, mul_add, mul_smul_comm, mul_smul_comm, C.property.1,
    map_add, τ.map_smul_of_tower, τ.map_smul_of_tower,
    trace_star_mul_denominator_inv C τ hτ r hr0 hr1]
  have ht : τ 1 = 1 := by simpa using hτ 0
  simp [ht]

end FreeGroupFactorMain.MobiusLog
namespace FreeGroupFactorMain.ElementalMobius
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

abbrev unitaryElemental (C : unitary A) : unitary (StarAlgebra.elemental ℂ (C : A)) :=
  ⟨⟨C, StarAlgebra.elemental.self_mem ℂ (C : A)⟩,
    ⟨Subtype.ext C.property.1, Subtype.ext C.property.2⟩⟩

def inclusion (C : unitary A) : (StarAlgebra.elemental ℂ (C : A)) →L[ℂ] A :=
  (StarAlgebra.elemental ℂ (C : A)).subtype.toAlgHom.toLinearMap.mkContinuous 1
    (fun _ => by simp)

omit [Nontrivial A] in
@[simp] theorem inclusion_apply (C : unitary A) (x : StarAlgebra.elemental ℂ (C : A)) :
    inclusion C x = (x : A) := rfl

omit [Nontrivial A] in
theorem unitaryElemental_zpow (C : unitary A) (m : ℤ) :
    (((unitaryElemental C ^ m : unitary (StarAlgebra.elemental ℂ (C : A))) :
      StarAlgebra.elemental ℂ (C : A)) : A) = ((C ^ m : unitary A) : A) := by
  let f : unitary (StarAlgebra.elemental ℂ (C : A)) →* unitary A :=
    Unitary.map (StarMonoidHom.ofClass (StarAlgebra.elemental ℂ (C : A)).subtype)
  exact congrArg (fun u : unitary A => (u : A)) (f.map_zpow (unitaryElemental C) m)

def value (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : unitary A :=
  Unitary.map (StarMonoidHom.ofClass (StarAlgebra.elemental ℂ (C : A)).subtype)
    (MobiusLog.mobius (unitaryElemental C) r hr0 hr1)

theorem trace (C : unitary A) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ m : ℤ, τ ((C^m : unitary A) : A) = if m = 0 then 1 else 0)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    τ (star (C : A) * (value C r hr0 hr1 : A)) = r := by
  have ht (m : ℤ) : (τ.comp (inclusion C)) ((unitaryElemental C^m : unitary _) :
      StarAlgebra.elemental ℂ (C : A)) = if m = 0 then 1 else 0 := by
    simp only [ContinuousLinearMap.comp_apply, inclusion_apply, unitaryElemental_zpow, hτ]
  exact MobiusLog.trace_star_mul_mobius (unitaryElemental C) (τ.comp (inclusion C)) ht r hr0 hr1

theorem bounded_log (C : unitary A) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ S : A, S ∈ StarAlgebra.elemental ℂ (C : A) ∧ IsSelfAdjoint S ∧ ‖S‖ ≤ Real.pi ∧
      NormedSpace.exp (Complex.I • S) = (value C r hr0 hr1 : A) := by
  let B := StarAlgebra.elemental ℂ (C : A)
  obtain ⟨S,hSn,hSexp⟩ := MobiusLog.mobius_bounded_log (unitaryElemental C) r hr0 hr1
  have hTsa : IsSelfAdjoint ((S : B) : A) := congrArg (fun x : B => (x : A)) S.property
  refine ⟨((S : B) : A), (S : B).property, hTsa, hSn, ?_⟩
  have hmap := congrArg (fun x : unitary B => ((x : B) : A)) hSexp
  change B.subtype (NormedSpace.exp (Complex.I • (S : B))) = _ at hmap
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  let : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B
  rw [NormedSpace.map_exp B.subtype continuous_subtype_val] at hmap
  exact hmap

end FreeGroupFactorMain.ElementalMobius
namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

theorem twoNorm_sub_unitary_sq (U V : unitary (groupVonNeumann G)) :
    twoNorm ((U : groupVonNeumann G) - (V : groupVonNeumann G)) ^ 2 =
      2 - 2 * (canonicalTrace (star (U : groupVonNeumann G) * (V : groupVonNeumann G))).re := by
  classical
  unfold twoNorm
  rw [map_sub, norm_sub_sq (𝕜 := ℂ)]
  change (twoNorm (U : groupVonNeumann G))^2 -
    2*(inner ℂ (groupL2 (U : groupVonNeumann G)) (groupL2 (V : groupVonNeumann G))).re +
    (twoNorm (V : groupVonNeumann G))^2 = _
  rw [twoNorm_unitary, twoNorm_unitary, canonicalTrace_star_mul_inner]
  simp only [groupL2_apply, deltaOne_eq]
  ring

def canonicalTraceContinuous : groupVonNeumann G →L[ℂ] ℂ :=
  (canonicalTraceLinear (G := G)).mkContinuous 1 (fun T => by
    change ‖canonicalTrace T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_canonicalTrace_le T)

@[simp] theorem canonicalTraceContinuous_apply (T : groupVonNeumann G) :
    canonicalTraceContinuous T = canonicalTrace T := rfl

theorem haar_approx_log (C : unitary (groupVonNeumann G))
    (hτ : ∀ m : ℤ, canonicalTrace ((C^m : unitary (groupVonNeumann G)) : groupVonNeumann G) =
      if m = 0 then 1 else 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : groupVonNeumann G,
      S ∈ StarAlgebra.elemental ℂ (C : groupVonNeumann G) ∧ IsSelfAdjoint S ∧
      ‖S‖ ≤ Real.pi ∧ twoNorm (NormedSpace.exp (Complex.I • S) - (C : groupVonNeumann G)) < ε := by
  classical
  let r : ℝ := 1 - min (ε^2/4) (1/2)
  have hpos : 0 < min (ε^2/4) (1/2:ℝ) := lt_min (by positivity) (by norm_num)
  have hr0 : 0 ≤ r := by dsimp [r]; have := min_le_right (ε^2/4) (1/2:ℝ); linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨S,hSm,hSsa,hSn,hSexp⟩ := ElementalMobius.bounded_log C r hr0 hr1
  refine ⟨S,hSm,hSsa,hSn,?_⟩
  rw [hSexp]
  have he := twoNorm_sub_unitary_sq C (ElementalMobius.value C r hr0 hr1)
  rw [← canonicalTraceContinuous_apply, ElementalMobius.trace C canonicalTraceContinuous hτ r hr0 hr1, Complex.ofReal_re] at he
  have hs : twoNorm ((ElementalMobius.value C r hr0 hr1 : groupVonNeumann G)-(C : groupVonNeumann G)) =
      twoNorm ((C : groupVonNeumann G)-(ElementalMobius.value C r hr0 hr1 : groupVonNeumann G)) := by
    unfold twoNorm
    rw [map_sub, map_sub, norm_sub_rev]
  rw [hs]
  have hm := min_le_left (ε^2/4) (1/2:ℝ)
  dsimp [r] at he
  nlinarith [norm_nonneg (groupL2 ((C : groupVonNeumann G)-(ElementalMobius.value C r hr0 hr1 : groupVonNeumann G)))]

end FreeGroupFactorMain

open scoped BigOperators
namespace FreeGroupFactorMain.LaurentApprox

section
variable {A : Type uA} [CStarAlgebra A]

def powers (C : unitary A) : Submonoid A where
  carrier := Set.range (fun m : ℤ => ((C^m : unitary A) : A))
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m+n, by simp [zpow_add]⟩

theorem adjoin_mem_span (C : unitary A) {x : A}
    (hx : x ∈ StarAlgebra.adjoin ℂ ({(C : A)} : Set A)) :
    x ∈ Submodule.span ℂ (Set.range (fun m : ℤ => ((C^m : unitary A) : A))) := by
  have hs : Submonoid.closure ({(C : A)} ∪ star ({(C : A)} : Set A)) ≤ powers C := by
    apply Submonoid.closure_le.mpr
    intro y hy
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.star_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by change (((C^(-1:ℤ) : unitary A) : A)) = _; simp only [zpow_neg_one]; rfl⟩
  exact Submodule.span_mono hs (by
    rw [← StarAlgebra.adjoin_eq_span]
    exact hx)

theorem approx_selfAdjoint (C : unitary A) {x : A}
    (hx : x ∈ StarAlgebra.elemental ℂ (C : A)) (hsa : IsSelfAdjoint x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : ℤ →₀ ℂ, IsSelfAdjoint (value C l) ∧ ‖value C l - x‖ < ε := by
  change x ∈ closure (StarAlgebra.adjoin ℂ ({(C : A)} : Set A) : Set A) at hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  let z : A := (1/2 : ℝ) • (y + star y)
  have hz : z ∈ StarAlgebra.adjoin ℂ ({(C : A)} : Set A) := by
    exact (StarAlgebra.adjoin ℂ ({(C : A)} : Set A)).smul_mem
      (by exact add_mem hy (star_mem hy)) (1/2 : ℝ)
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_mem_span C hz)
  have hl' : value C l = z := hl
  refine ⟨l, ?_, ?_⟩
  · rw [hl']
    show star z = z
    simp [z, add_comm]
  · rw [hl']
    have hz' : z - x = (1/2:ℝ) • ((y-x) + star (y-x)) := by
      simp only [z, star_sub, hsa.star_eq]
      module
    rw [hz', norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hn := norm_add_le (y-x) (star (y-x))
    rw [norm_star] at hn
    have hh : ‖y-x‖ < ε := by simpa only [dist_eq_norm, norm_sub_rev] using hxy
    nlinarith

theorem trace_value (C : unitary A) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ m : ℤ, τ ((C^m : unitary A) : A) = if m = 0 then 1 else 0)
    (l : ℤ →₀ ℂ) : τ (value C l) = l 0 := by
  classical
  simp only [value, Finsupp.sum, map_sum, map_smul, hτ]
  simp [smul_eq_mul, mul_ite, eq_comm]

theorem approx_selfAdjoint_exp (C : unitary A) {x : A}
    (hx : x ∈ StarAlgebra.elemental ℂ (C : A)) (hsa : IsSelfAdjoint x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : ℤ →₀ ℂ, IsSelfAdjoint (value C l) ∧ ‖value C l‖ ≤ ‖x‖+1 ∧
      ‖NormedSpace.exp (Complex.I • value C l) - NormedSpace.exp (Complex.I • x)‖ < ε := by
  have hc : ContinuousAt (fun y : A => NormedSpace.exp (Complex.I • y)) x := by
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).continuousAt.comp
      (continuous_const_smul _).continuousAt
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨l, hsa', hl⟩ := approx_selfAdjoint C hx hsa (ε := min δ 1) (lt_min hδ (by norm_num))
  refine ⟨l, hsa', ?_, ?_⟩
  · have hh := norm_add_le (value C l-x) x
    rw [sub_add_cancel] at hh
    have := (lt_min_iff.mp hl).2
    linarith
  · simpa only [dist_eq_norm] using
      hd (by simpa only [dist_eq_norm] using (lt_min_iff.mp hl).1)

end

variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

theorem center (C : unitary A) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ m : ℤ, τ ((C^m : unitary A) : A) = if m = 0 then 1 else 0)
    (hstar : ∀ x, τ (star x) = star (τ x)) (hb : ∀ x, ‖τ x‖ ≤ ‖x‖)
    (l : ℤ →₀ ℂ) (hsa : IsSelfAdjoint (value C l)) (K : ℝ) (hn : ‖value C l‖ ≤ K) :
    ∃ k : ℤ →₀ ℂ, k 0 = 0 ∧ IsSelfAdjoint (value C k) ∧ ‖value C k‖ ≤ 2*K ∧
      ∃ z : unitary ℂ, NormedSpace.exp (Complex.I • value C k) =
        (z : ℂ) • NormedSpace.exp (Complex.I • value C l) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  have hre : IsSelfAdjoint (l 0) := by
    change star (l 0) = l 0
    rw [← trace_value C τ hτ l, ← hstar, hsa.star_eq]
  have hbn : ‖l 0‖ ≤ ‖value C l‖ := by rw [← trace_value C τ hτ l]; exact hb _
  let k : ℤ →₀ ℂ := l - Finsupp.single 0 (l 0)
  have hk : value C k = value C l - (l 0) • (1 : A) := by
    simp only [k,value_sub,value_single,zpow_zero,Submonoid.coe_one]
  refine ⟨k,by simp [k],?_,?_,?_⟩
  · rw [hk]
    exact hsa.sub (hre.smul (IsSelfAdjoint.one A))
  · rw [hk]
    calc
      ‖value C l - (l 0) • (1 : A)‖ ≤ ‖value C l‖ + ‖(l 0) • (1 : A)‖ := norm_sub_le _ _
      _ ≤ ‖value C l‖ + ‖l 0‖ := by
        gcongr
        simp only [norm_smul, norm_one, mul_one, le_refl]
      _ ≤ 2*K := by linarith
  · let z : unitary ℂ := selfAdjoint.expUnitary ⟨-(l 0), hre.neg⟩
    refine ⟨z,?_⟩
    have he : NormedSpace.exp ((Complex.I * (-(l 0))) • (1 : A)) = (z : ℂ) • (1 : A) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm]
      exact Algebra.algebraMap_eq_smul_one _
    rw [hk]
    have hs : Complex.I • (value C l - (l 0) • (1 : A)) =
        (Complex.I * (-(l 0))) • (1 : A) + Complex.I • value C l := by module
    rw [hs, NormedSpace.exp_add_of_commute, he, smul_mul_assoc, one_mul]
    exact (Commute.one_left (Complex.I • value C l)).smul_left _

end FreeGroupFactorMain.LaurentApprox

namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

theorem haar_centered_laurent (C : unitary (groupVonNeumann G))
    (hτ : ∀ m : ℤ, canonicalTrace ((C^m : unitary (groupVonNeumann G)) : groupVonNeumann G) =
      if m = 0 then 1 else 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℤ →₀ ℂ, k 0 = 0 ∧ IsSelfAdjoint (LaurentApprox.value C k) ∧
      ‖LaurentApprox.value C k‖ ≤ 2*(Real.pi+1) ∧ ∃ z : unitary ℂ,
      twoNorm (NormedSpace.exp (Complex.I • LaurentApprox.value C k) - (z : ℂ) • (C : groupVonNeumann G)) < ε := by
  obtain ⟨S,hSm,hSsa,hSn,hSe⟩ := haar_approx_log C hτ (half_pos hε)
  obtain ⟨l,hlS,hln,hle⟩ := LaurentApprox.approx_selfAdjoint_exp C hSm hSsa (half_pos hε)
  obtain ⟨k,hk0,hkS,hkn,z,hze⟩ := LaurentApprox.center C canonicalTraceContinuous hτ
    canonicalTrace_star norm_canonicalTrace_le l hlS (Real.pi+1) (hln.trans (by linarith))
  refine ⟨k,hk0,hkS,hkn,z,?_⟩
  have hsmul : (z : ℂ) •
      (NormedSpace.exp (Complex.I • LaurentApprox.value C l) - (C : groupVonNeumann G)) =
      (z : ℂ) • NormedSpace.exp (Complex.I • LaurentApprox.value C l) -
        (z : ℂ) • (C : groupVonNeumann G) :=
    smul_sub (z : ℂ) (NormedSpace.exp (Complex.I • LaurentApprox.value C l))
      (C : groupVonNeumann G)
  rw [hze, ← hsmul]
  change ‖groupL2 ((z : ℂ) • _)‖ < ε
  rw [map_smul, norm_smul, CStarRing.norm_coe_unitary, one_mul]
  have he : NormedSpace.exp (Complex.I • LaurentApprox.value C l) - (C : groupVonNeumann G) =
      (NormedSpace.exp (Complex.I • LaurentApprox.value C l) - NormedSpace.exp (Complex.I • S)) +
      (NormedSpace.exp (Complex.I • S) - (C : groupVonNeumann G)) := by abel
  rw [he, map_add]
  have ht := norm_add_le (groupL2 (NormedSpace.exp (Complex.I • LaurentApprox.value C l) - NormedSpace.exp (Complex.I • S)))
    (groupL2 (NormedSpace.exp (Complex.I • S) - (C : groupVonNeumann G)))
  have hb := twoNorm_le_norm (NormedSpace.exp (Complex.I • LaurentApprox.value C l) - NormedSpace.exp (Complex.I • S))
  change ‖groupL2 (NormedSpace.exp (Complex.I • S) - (C : groupVonNeumann G))‖ < ε/2 at hSe
  linarith

end FreeGroupFactorMain

end

end OAI
end

theorem solution.{uG} : type_of% @OAI.FreeGroupFactorMain.haar_centered_laurent.{uG} := @OAI.FreeGroupFactorMain.haar_centered_laurent.{uG}
