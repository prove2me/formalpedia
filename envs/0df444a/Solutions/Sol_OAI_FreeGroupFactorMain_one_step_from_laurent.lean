-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.one_step_from_laurent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:20:35.447316+00:00
-- url     : https://prove2.me/submissions/bc52886c-a03b-4e3f-b462-02feebea1451
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_laurent_flow_displacement
import Theorems.Thm_OAI_FreeGroupFactorMain_gauged_nielsen_iso

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

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

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

theorem canonicalTrace_mul {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) : canonicalTrace (T * U) = canonicalTrace (U * T) := by
  have he (T U : groupVonNeumann G) :
      canonicalTrace (T * U) = ∑' x : G,
        ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x := by
    rw [← star_star T, canonicalTrace_star_mul_inner]
    change (∑' x, inner ℂ (((star T : GroupOperator G) deltaOne) x)
      (((U : GroupOperator G) deltaOne) x)) = _
    apply tsum_congr
    intro x
    rw [groupVN_star_coefficient]
    simp [RCLike.inner_apply, mul_comm]
  rw [he, he]
  simpa only [Equiv.inv_apply, inv_inv, mul_comm] using
    ((Equiv.inv G).tsum_eq (fun x =>
      ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x)).symm

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

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

theorem twoNorm_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm (star T) = twoNorm T := by
  classical
  have hsq : (twoNorm (star T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, star_star]
    exact canonicalTrace_mul T (star T)
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (star T)), norm_nonneg (groupL2 T)]

theorem twoNorm_mul_unitary_right {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm (T*(U : groupVonNeumann G)) = twoNorm T := by
  rw [← twoNorm_star, star_mul]
  change twoNorm (((star U : unitary (groupVonNeumann G)) : groupVonNeumann G) * star T) = _
  rw [twoNorm_mul_unitary_left, twoNorm_star]

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

theorem twoNorm_add_le (x y : groupVonNeumann G) : twoNorm (x+y) ≤ twoNorm x + twoNorm y := by
  change ‖groupL2 (x+y)‖ ≤ _
  rw [map_add]
  exact norm_add_le _ _

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

theorem trace_symm {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (T : groupVonNeumann G) :
    canonicalTrace (γ.symm T) = canonicalTrace T := by
  simpa only [γ.apply_symm_apply] using (ht (γ.symm T)).symm

theorem norm_symm_sub {A : Type uA} [CStarAlgebra A]
    (γ : A ≃⋆ₐ[ℂ] A) (X Y : A) : ‖γ.symm X - Y‖ = ‖X - γ Y‖ := by
  have he : γ.symm (X - γ Y) = γ.symm X - Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,StarAlgEquiv.norm_map]

theorem twoNorm_symm_sub {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (X Y : groupVonNeumann G) :
    twoNorm (γ.symm X-Y) = twoNorm (X-γ Y) := by
  have he : γ.symm (X-γ Y) = γ.symm X-Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,twoNorm_iso γ.symm (trace_symm γ ht)]

theorem firstCoefficients_norm_le {n : ℕ} (h : Coeff (FreeGroup (Fin n))) (j : Fin n) :
    coefficientNorm (firstCoefficients h j) ≤ coefficientNorm h := by
  unfold firstCoefficients
  split_ifs
  · exact le_rfl
  · simp only [coefficientNorm,Finsupp.sum_zero_index,Real.sqrt_zero]
    exact Real.sqrt_nonneg _

theorem one_step_generator_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (A : groupVonNeumann G) (hγ : γ A = A)
    {K ε c : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hb : ‖β A-A‖ ≤ 3*K*c) (hc : c < (ε/2)/(3*K)) :
    ‖γ.symm (β A)-A‖ < ε := by
  rw [norm_symm_sub,hγ]
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

theorem one_step_word_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (hγt : ∀ T, canonicalTrace (γ T) = canonicalTrace T)
    (C W : unitary (groupVonNeumann G)) (E : groupVonNeumann G) (z : unitary ℂ)
    (hγC : γ (C : groupVonNeumann G) = (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)))
    {K ε c : ℝ} (hK : 0 < K)
    (hb : ‖β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)‖ ≤ 3*K*c)
    (hc : c < (ε/2)/(3*K)) (hze : twoNorm (E-(z : ℂ) • (C : groupVonNeumann G)) < ε/2) :
    twoNorm (γ.symm (β (W : groupVonNeumann G))-(C : groupVonNeumann G)) < ε := by
  rw [twoNorm_symm_sub γ hγt,hγC]
  have he : β (W : groupVonNeumann G) - (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)) =
      (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)) +
      (E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G) := by
    simp only [sub_mul,smul_mul_assoc]
    abel
  rw [he]
  have ht := Generation.twoNorm_add_le
    (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
    ((E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G))
  rw [twoNorm_mul_unitary_right] at ht
  have hle := twoNorm_le_norm (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

theorem one_step_from_laurent (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n))) l) - (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  let K : ℝ := 2*(Real.pi+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨β,hβt,hβn,_hβC,hβgen,hβword⟩ :=
    laurent_flow_displacement (ι := Fin n) (firstCoefficients h) l hl0 hlS K hK.le hln
  obtain ⟨γ,hγt,_hγn,hγi,hγgen,hγC⟩ := gauged_nielsen_iso (ι := Fin n) w z
  have hnormal : @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
      (groupUltraweakTopology (FreeGroup (Option (Fin n)))) (β.trans γ.symm) := by
    let : TopologicalSpace (groupVonNeumann (FreeGroup (Option (Fin n)))) :=
      groupUltraweakTopology (FreeGroup (Option (Fin n)))
    exact hγi.comp hβn
  refine ⟨β.trans γ.symm,?_,hnormal,w,?_,?_⟩
  · intro T
    change canonicalTrace (γ.symm (β T)) = canonicalTrace T
    rw [trace_symm γ hγt,hβt]
  · intro j
    exact one_step_generator_estimate (G := FreeGroup (Option (Fin n))) β γ _ (hγgen j) hK hε (hβgen j)
      ((firstCoefficients_norm_le h j).trans_lt hh)
  · exact one_step_word_estimate (G := FreeGroup (Option (Fin n))) β γ hγt (generatorUnitary (none : Option (Fin n)))
      (groupUnitaryUHom (FreeGroup (Option (Fin n))) (FreeGroup.map Option.some w))
      _ z hγC hK (hβword w) hw hze

end FreeGroupFactorMain

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.one_step_from_laurent := @OAI.FreeGroupFactorMain.one_step_from_laurent
