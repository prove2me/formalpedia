-- Prove2me | solution 1 for LanglandsTunnell.exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/59603261-55cf-556f-974d-035577cb2446

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open HeckeIntegralSeam

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm Matrix

namespace DeterminantCharacter

section Generic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGenAt (v : HeightOneSpectrum R) (t : (v.adicCompletion K)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt R K v t)
      = Units.map (finIncl R K) (localUnit R K v t) :=
  det_diagOne _

private theorem det_heckeGen (v : HeightOneSpectrum R) :
    Matrix.GeneralLinearGroup.det (heckeGen R K v)
      = Units.map (finIncl R K) (localUnit R K v (uniformizerUnit K v)) :=
  det_heckeGenAt v _

private theorem val_centralScalar (z : (AdeleRing R K)ˣ) :
    (centralScalar R K z : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) :=
  rfl

private theorem val_centralScalar_inv (z : (AdeleRing R K)ˣ) :
    (((centralScalar R K z)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) :=
  rfl

private theorem centralScalar_map_algebraMap (k : Kˣ) :
    centralScalar R K (Units.map (algebraMap K (AdeleRing R K)) k)
      = globalPoints R K (Matrix.GeneralLinearGroup.scalar (Fin 2) k) := by
  refine Units.ext ?_
  rw [val_centralScalar, Units.coe_map]
  show Matrix.scalar (Fin 2) (algebraMap K (AdeleRing R K) (k : K))
    = (algebraMap K (AdeleRing R K)).mapMatrix (Matrix.scalar (Fin 2) (k : K))
  rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem centralScalar_mul_comm (z : (AdeleRing R K)ˣ) (g : AdelicGL2 R K) :
    centralScalar R K z * g = g * centralScalar R K z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_centralScalar]
  have h : Commute (Matrix.scalar (Fin 2) (z : AdeleRing R K)) g.val :=
    Matrix.scalar_commute (n := Fin 2) (z : AdeleRing R K) (fun r' => Commute.all (z : AdeleRing R K) r') g.val
  exact h.eq

private theorem continuous_centralScalar : Continuous (centralScalar R K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (Units.val ∘ centralScalar R K)
        = fun z : (AdeleRing R K)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing R K) :=
      funext fun z => by rw [Function.comp_apply, val_centralScalar, Matrix.scalar_apply]
    rw [h]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · have h : (fun z : (AdeleRing R K)ˣ => (((centralScalar R K z)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) _))
        = fun z : (AdeleRing R K)ˣ => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) :=
      funext fun z => by rw [val_centralScalar_inv, Matrix.scalar_apply]
    rw [h]
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

end Generic

section NumberField

variable {F : Type} [Field F] [NumberField F]

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 v = WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 v

private def IsLevelUnitIdele (𝔣 : Ideal (𝓞 F)) (u : (AdeleRing (𝓞 F) F)ˣ) : Prop :=
  (u : AdeleRing (𝓞 F) F).1 = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((u : AdeleRing (𝓞 F) F).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 F) F).2 v - 1) ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ))

private theorem admitsModulus_of_forall {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 F)}
    (h : ∀ u, IsLevelUnitIdele 𝔣 u → χ u = 1) : HeckeCharacter.AdmitsModulus F χ 𝔣 :=
  fun u h1 h2 => h u ⟨h1, h2⟩

private theorem snd_inv_apply (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) * ((u : AdeleRing (𝓞 F) F).2 v) = 1 := by
  have h := congrArg (fun a : AdeleRing (𝓞 F) F => (finAdeleEval (𝓞 F) F v) ((adeleFin (𝓞 F) F) a)) u.inv_mul
  simpa only [map_mul, map_one, finAdeleEval_apply, adeleFin_apply] using h

private theorem IsLevelUnitIdele.inv {𝔣 : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ} (hu : IsLevelUnitIdele 𝔣 u) :
    IsLevelUnitIdele 𝔣 u⁻¹ := by
  refine ⟨?_, fun v => ?_⟩
  · have h := congrArg (fun a : AdeleRing (𝓞 F) F => (adeleArch (𝓞 F) F) a) u.inv_mul
    simp only [map_mul, map_one, adeleArch_apply, hu.1, mul_one] at h
    exact h
  · obtain ⟨hv1, hv2⟩ := hu.2 v
    have hprod := snd_inv_apply u v
    set y := ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
    set x := (u : AdeleRing (𝓞 F) F).2 v
    have hy : Valued.v y = 1 := by
      have := congrArg Valued.v hprod
      rw [Valuation.map_mul, hv1, mul_one, Valuation.map_one] at this
      exact this
    refine ⟨hy, ?_⟩
    have hsub : y - 1 = y * (1 - x) := by rw [mul_sub, mul_one, hprod]
    rw [hsub, Valuation.map_mul, hy, one_mul, Valuation.map_sub_swap]
    exact hv2

private theorem glFin_centralScalar (u : (AdeleRing (𝓞 F) F)ˣ) :
    (glFin (𝓞 F) F (centralScalar (𝓞 F) F u) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = Matrix.scalar (Fin 2) ((u : AdeleRing (𝓞 F) F).2) := by
  refine Matrix.ext fun i j => ?_
  rw [glFin_apply, val_centralScalar, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  split_ifs <;> rfl

private theorem isLevelOneMatrix_scalar {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : IsLevelUnitIdele 𝔣 u) :
    IsLevelOneMatrix (𝓞 F) F 𝔣 (Matrix.scalar (Fin 2) ((u : AdeleRing (𝓞 F) F).2)) := by
  have hint : (u : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hu.2 v).1.le
  have hball : (u : AdeleRing (𝓞 F) F).2 - 1 ∈ idealBall (𝓞 F) F 𝔣 := fun v => by
    rw [coe_sub_apply, coe_one_apply, idealBound_eq_exp_neg_idealMultiplicity h𝔣]
    exact (hu.2 v).2
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hint
    · exact zero_mem_integralFiniteAdeles
  · show Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F).2 1 0 ∈ idealBall (𝓞 F) F 𝔣
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
    exact zero_mem_idealBall 𝔣
  · show Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F).2 1 1 - 1 ∈ idealBall (𝓞 F) F 𝔣
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact hball

private theorem centralScalar_mem_levelOne {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : IsLevelUnitIdele 𝔣 u) : centralScalar (𝓞 F) F u ∈ levelOne (𝓞 F) F 𝔣 := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff, ← map_inv, ← map_inv, glFin_centralScalar, glFin_centralScalar]
  exact ⟨isLevelOneMatrix_scalar h𝔣 hu, isLevelOneMatrix_scalar h𝔣 hu.inv⟩

private theorem centralScalar_mem_finiteAdelicGL2Subgroup {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : (u : AdeleRing (𝓞 F) F).1 = 1) : centralScalar (𝓞 F) F u ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one, val_centralScalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact hu
  · rfl

private theorem admitsModulus_of_right_invariant {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0)
    (hχ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((χ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 F) F z * g₀) / φ g₀)
    (hright : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F 𝔣 ⊓ finiteAdelicGL2Subgroup F, φ (g * k) = φ g) :
    HeckeCharacter.AdmitsModulus F χ 𝔣 := by
  refine admitsModulus_of_forall fun u hu => Units.ext ?_
  rw [hχ, Units.val_one, centralScalar_mul_comm,
    hright g₀ _ (Subgroup.mem_inf.2 ⟨centralScalar_mem_levelOne h𝔣 hu, centralScalar_mem_finiteAdelicGL2Subgroup hu.1⟩),
    div_self hg₀]

private theorem isIdeleClassChar_of_left_invariant
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0)
    (hχ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((χ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 F) F z * g₀) / φ g₀)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g) :
    IsIdeleClassChar (𝓞 F) F χ := by
  intro k
  refine Units.ext ?_
  rw [hχ, Units.val_one, centralScalar_map_algebraMap, hleft, div_self hg₀]

private theorem continuous_of_central_quotient
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g₀ : AdelicGL2 (𝓞 F) F)
    (hχ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((χ z : ℂˣ) : ℂ) = φ (centralScalar (𝓞 F) F z * g₀) / φ g₀) :
    Continuous χ := by
  have hval : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((χ z : ℂˣ) : ℂ) := by
    simp only [hχ]
    exact (hφ.comp (continuous_centralScalar.mul continuous_const)).div_const _
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hval.inv₀ fun z => (χ z).ne_zero

end NumberField

end DeterminantCharacter

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open scoped Topology

namespace DeterminantCharacter

section Norm

variable {F : Type} [Field F] [NumberField F]

private theorem arch_apply_mul (x y : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((x * y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = (x : AdeleRing (𝓞 F) F).1 w * (y : AdeleRing (𝓞 F) F).1 w := by
  have h := map_mul ((archEval F w).comp (adeleArch (𝓞 F) F)) (x : AdeleRing (𝓞 F) F) (y : AdeleRing (𝓞 F) F)
  simpa only [RingHom.comp_apply, archEval_apply, adeleArch_apply, Units.val_mul] using h

private theorem fin_apply_mul (x y : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((x * y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = (x : AdeleRing (𝓞 F) F).2 v * (y : AdeleRing (𝓞 F) F).2 v := by
  have h := map_mul ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)) (x : AdeleRing (𝓞 F) F) (y : AdeleRing (𝓞 F) F)
  simpa only [RingHom.comp_apply, finAdeleEval_apply, adeleFin_apply, Units.val_mul] using h

private theorem arch_apply_mul_inv (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (x : AdeleRing (𝓞 F) F).1 w * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
  rw [← arch_apply_mul, mul_inv_cancel, Units.val_one]; rfl

private theorem fin_apply_mul_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  rw [← fin_apply_mul, mul_inv_cancel, Units.val_one]; rfl

private theorem arch_apply_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (x : AdeleRing (𝓞 F) F).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (arch_apply_mul_inv x w)

private theorem fin_apply_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (fin_apply_mul_inv x v)

private theorem valued_eq_one_of_mul_eq_one {v : HeightOneSpectrum (𝓞 F)} {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : a * b = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  have h : Valued.v a * Valued.v b = 1 := by rw [← Valuation.map_mul, hab, Valuation.map_one]
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v a * Valued.v b := h.symm
    _ ≤ Valued.v a * 1 := by gcongr
    _ = Valued.v a := mul_one _

private theorem norm_eq_one_of_valued_eq_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a = 1) : ‖a‖ = 1 := by
  rw [FinitePlace.norm_def, ha, map_one, NNReal.coe_one]

private theorem eventually_valued_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v ((x : AdeleRing (𝓞 F) F).2 v) = 1 := by
  have hx : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (x : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (x : AdeleRing (𝓞 F) F).2.2
  have hy : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2.2
  filter_upwards [hx, hy] with v hxv hyv
  exact valued_eq_one_of_mul_eq_one ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hxv)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hyv) (fin_apply_mul_inv x v)

private theorem hasFiniteMulSupport_norm_fin (x : (AdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(x : AdeleRing (𝓞 F) F).2 v‖).HasFiniteMulSupport := by
  refine (Filter.eventually_cofinite.mp ((eventually_valued_eq_one x).mono fun v hv => ?_))
  exact norm_eq_one_of_valued_eq_one hv

omit [NumberField F] in

private theorem arch_norm_mul (w : InfinitePlace F) (a b : w.Completion) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  haveI : NormMulClass w.Completion := NormedDivisionRing.toNormMulClass
  exact norm_mul a b

omit [NumberField F] in
private theorem arch_norm_one (w : InfinitePlace F) : ‖(1 : w.Completion)‖ = 1 := by
  have h := arch_norm_mul w 1 1
  rw [show (1 : w.Completion) * 1 = 1 from mul_one 1] at h
  haveI : NeZero (1 : w.Completion) := NeZero.one
  exact (mul_right_eq_self₀.mp h.symm).resolve_right (norm_pos_iff.mpr one_ne_zero).ne'

private def archAbs (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ∏ w : InfinitePlace F, ‖(x : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult

private def finAbs (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : AdeleRing (𝓞 F) F).2 v‖

private def ideleAbs (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ := archAbs x * finAbs x

private theorem archAbs_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < archAbs x :=
  Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (arch_apply_ne_zero x w)) _

private theorem finAbs_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < finAbs x := by
  unfold finAbs
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (hasFiniteMulSupport_norm_fin x).toFinset)
    (by simp only [Set.Finite.coe_toFinset, subset_refl])]
  exact Finset.prod_pos fun v _ => norm_pos_iff.mpr (fin_apply_ne_zero x v)

private theorem ideleAbs_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < ideleAbs x :=
  mul_pos (archAbs_pos x) (finAbs_pos x)

private theorem archAbs_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : archAbs (x * y) = archAbs x * archAbs y := by
  unfold archAbs
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [arch_apply_mul, arch_norm_mul, mul_pow]

private theorem finAbs_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : finAbs (x * y) = finAbs x * finAbs y := by
  unfold finAbs
  rw [← finprod_mul_distrib (hasFiniteMulSupport_norm_fin x) (hasFiniteMulSupport_norm_fin y)]
  exact finprod_congr fun v => by rw [fin_apply_mul, norm_mul]

private theorem ideleAbs_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : ideleAbs (x * y) = ideleAbs x * ideleAbs y := by
  unfold ideleAbs
  rw [archAbs_mul, finAbs_mul]; ring

private theorem archAbs_eq_one_of_fst_eq_one {x : (AdeleRing (𝓞 F) F)ˣ} (hx : (x : AdeleRing (𝓞 F) F).1 = 1) :
    archAbs x = 1 := by
  unfold archAbs
  refine Finset.prod_eq_one fun w _ => ?_
  rw [hx]
  show ‖(1 : w.Completion)‖ ^ w.mult = 1
  rw [arch_norm_one, one_pow]

private theorem ideleAbs_eq_one_of_isLevelUnitIdele {𝔣 : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : IsLevelUnitIdele 𝔣 u) : ideleAbs u = 1 := by
  unfold ideleAbs
  rw [archAbs_eq_one_of_fst_eq_one hu.1, one_mul]
  exact finprod_eq_one_of_forall_eq_one fun v => norm_eq_one_of_valued_eq_one (hu.2 v).1

private theorem ideleAbs_finIncl_localUnit (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ideleAbs (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) = ‖(t : v.adicCompletion F)‖ := by
  unfold ideleAbs
  rw [archAbs_eq_one_of_fst_eq_one (by rw [Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _), one_mul]
  unfold finAbs
  rw [finprod_eq_single _ v]
  · rw [Units.coe_map]
    show ‖((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖ = _
    rw [localUnit_apply_self]
  · intro w hw
    rw [Units.coe_map]
    show ‖((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w‖ = 1
    rw [localUnit_apply_of_ne (𝓞 F) F v t hw, norm_one]

private theorem norm_uniformizerUnit (v : HeightOneSpectrum (𝓞 F)) :
    ‖(uniformizerUnit F v : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
  rw [FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  have hu : WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ))) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.unzero_coe _
  rw [hu, toAdd_ofAdd, _root_.zpow_neg_one]
  simp

private theorem ideleAbs_map_algebraMap (k : Fˣ) :
    ideleAbs (F := F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) k) = 1 := by
  have hk : (k : F) ≠ 0 := k.ne_zero
  have harch : archAbs (F := F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) k)
      = ∏ w : InfinitePlace F, w (k : F) ^ w.mult := by
    unfold archAbs
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Units.coe_map]
    show ‖((algebraMap F (AdeleRing (𝓞 F) F)) (k : F)).1 w‖ ^ w.mult = _
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe]
    simp
  have hfin : finAbs (F := F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) k) = ∏ᶠ w : FinitePlace F, w (k : F) := by
    unfold finAbs
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun w : FinitePlace F => w (k : F))]
    refine finprod_congr fun v => ?_
    rw [Units.coe_map, FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  unfold ideleAbs
  rw [harch, hfin]
  exact prod_abs_eq_one hk

private theorem continuous_archAbs : Continuous (archAbs (F := F)) := by
  unfold archAbs
  refine continuous_finsetProd _ fun w _ => ?_
  exact (((continuous_archEval F w).comp ((continuous_adeleArch (𝓞 F) F).comp Units.continuous_val)).norm).pow _

private def unitIdeles : Set (AdeleRing (𝓞 F) F)ˣ :=
  {x | (x : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F ∧
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F}

private theorem isOpen_unitIdeles : IsOpen (unitIdeles (F := F)) := by
  refine IsOpen.inter ?_ ?_
  · exact (isOpen_integralFiniteAdeles (𝓞 F) F).preimage ((continuous_adeleFin (𝓞 F) F).comp Units.continuous_val)
  · exact (isOpen_integralFiniteAdeles (𝓞 F) F).preimage ((continuous_adeleFin (𝓞 F) F).comp Units.continuous_coe_inv)

private theorem one_mem_unitIdeles : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ unitIdeles := by
  refine ⟨?_, ?_⟩
  · show ((1 : AdeleRing (𝓞 F) F)).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F
    exact one_mem_integralFiniteAdeles
  · rw [inv_one]
    show ((1 : AdeleRing (𝓞 F) F)).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F
    exact one_mem_integralFiniteAdeles

private theorem finAbs_eq_one_of_mem_unitIdeles {z : (AdeleRing (𝓞 F) F)ˣ} (hz : z ∈ unitIdeles) : finAbs z = 1 :=
  finprod_eq_one_of_forall_eq_one fun v => norm_eq_one_of_valued_eq_one
    (valued_eq_one_of_mul_eq_one ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hz.1 v))
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hz.2 v)) (fin_apply_mul_inv z v))

private theorem isLocallyConstant_finAbs : IsLocallyConstant (finAbs (F := F)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hcont : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => x⁻¹ * y := continuous_const.mul continuous_id
  have hopen : IsOpen ((fun y : (AdeleRing (𝓞 F) F)ˣ => x⁻¹ * y) ⁻¹' unitIdeles) := isOpen_unitIdeles.preimage hcont
  have hmem : x ∈ (fun y : (AdeleRing (𝓞 F) F)ˣ => x⁻¹ * y) ⁻¹' unitIdeles := by
    rw [Set.mem_preimage, inv_mul_cancel]
    exact one_mem_unitIdeles
  refine Filter.eventually_of_mem (hopen.mem_nhds hmem) fun y hy => ?_
  rw [Set.mem_preimage] at hy
  have hy' : y = x * (x⁻¹ * y) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hy', finAbs_mul, finAbs_eq_one_of_mem_unitIdeles hy, mul_one]

private theorem continuous_ideleAbs : Continuous (ideleAbs (F := F)) :=
  continuous_archAbs.mul isLocallyConstant_finAbs.continuous

private def normChar : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((ideleAbs x : ℝ) : ℂ) (by exact_mod_cast (ideleAbs_pos x).ne')
  map_one' := by
    refine Units.ext ?_
    have h : ideleAbs (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
      have := ideleAbs_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
      rw [mul_one] at this
      exact (mul_right_eq_self₀.mp this.symm).resolve_right (ideleAbs_pos 1).ne'
    simp [h]
  map_mul' x y := by
    refine Units.ext ?_
    simp [ideleAbs_mul]

private theorem normChar_apply (x : (AdeleRing (𝓞 F) F)ˣ) : ((normChar x : ℂˣ) : ℂ) = ((ideleAbs x : ℝ) : ℂ) := rfl

private theorem continuous_normChar : Continuous (normChar (F := F)) := by
  have hval : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((normChar x : ℂˣ) : ℂ) := by
    simp only [normChar_apply]
    exact Complex.continuous_ofReal.comp continuous_ideleAbs
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hval.inv₀ fun x => (normChar x).ne_zero

private theorem normChar_eq_one_of_isLevelUnitIdele {𝔣 : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : IsLevelUnitIdele 𝔣 u) : normChar u = 1 := by
  refine Units.ext ?_
  rw [normChar_apply, ideleAbs_eq_one_of_isLevelUnitIdele hu, Units.val_one]
  simp

private theorem isIdeleClassChar_normChar : IsIdeleClassChar (𝓞 F) F (normChar (F := F)) := by
  intro k
  refine Units.ext ?_
  rw [normChar_apply, ideleAbs_map_algebraMap, Units.val_one]
  simp

private theorem normChar_det_heckeGen (v : HeightOneSpectrum (𝓞 F)) :
    ((normChar (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ)
      = (HeckeEigensystem.cNorm (F := F) v)⁻¹ := by
  rw [det_heckeGen, normChar_apply, ideleAbs_finIncl_localUnit, norm_uniformizerUnit, HeckeEigensystem.cNorm]
  push_cast
  rfl

end Norm

end DeterminantCharacter

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

namespace DeterminantCharacter

private def TrivialityCriterion (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), Continuous θ → IsIdeleClassChar (𝓞 F) F θ →
    ∀ (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → HeckeCharacter.AdmitsModulus F θ 𝔣 →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) →
      θ = 1

variable {F : Type} [Field F] [NumberField F]

private theorem mul_inv_normChar_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((χ * (normChar (F := F))⁻¹) x : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ) * (((normChar x : ℂˣ) : ℂ))⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem exists_eta (hcrit : TrivialityCriterion F) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous χ)
    (hclass : IsIdeleClassChar (𝓞 F) F χ) {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F χ 𝔣)
    (b : HeightOneSpectrum (𝓞 F) → ℂ) (E : Finset (HeightOneSpectrum (𝓞 F)))
    (hval : ∀ v ∉ E, ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ)
      = (HeckeEigensystem.cNorm v)⁻¹ * b v)
    (n : ℕ) (hn : 0 < n) (hbn : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, b v ^ n = 1) :
    ∃ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar F η ∧
      (∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = b v := by
  obtain ⟨Sb, hSb⟩ := hbn

  have hηval : ∀ v ∉ E,
      (((χ * (normChar (F := F))⁻¹) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = b v := by
    intro v hv
    rw [mul_inv_normChar_apply, hval v hv, normChar_det_heckeGen, inv_inv, mul_comm, ← mul_assoc,
      mul_inv_cancel₀ (HeckeEigensystem.cNorm_ne_zero v), one_mul]

  have hηclass : IsIdeleClassChar (𝓞 F) F (χ * (normChar (F := F))⁻¹) := by
    intro k
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hclass k, isIdeleClassChar_normChar k, inv_one, mul_one]

  have hηmod : HeckeCharacter.AdmitsModulus F (χ * (normChar (F := F))⁻¹) 𝔣 := by
    refine admitsModulus_of_forall fun u hu => ?_
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hmod u hu.1 hu.2, normChar_eq_one_of_isLevelUnitIdele hu,
      inv_one, mul_one]

  have hηcont : Continuous (χ * (normChar (F := F))⁻¹) := by
    have h : ⇑(χ * (normChar (F := F))⁻¹) = fun x => χ x * (normChar x)⁻¹ :=
      funext fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [h]
    exact hcont.mul continuous_normChar.inv

  have hpow : (χ * (normChar (F := F))⁻¹) ^ n = 1 := by
    classical
    refine hcrit _ ?_ ?_ 𝔣 h𝔣 ?_ (E ∪ Sb) ?_
    · have h : ⇑((χ * (normChar (F := F))⁻¹) ^ n) = fun x => (χ * (normChar (F := F))⁻¹) x ^ n :=
        funext fun x => MonoidHom.pow_apply _ n x
      rw [h]
      exact hηcont.pow n
    · intro k
      rw [MonoidHom.pow_apply, hηclass k, one_pow]
    · refine admitsModulus_of_forall fun u hu => ?_
      rw [MonoidHom.pow_apply, hηmod u hu.1 hu.2, one_pow]
    · intro v hv
      rw [Finset.mem_union, not_or] at hv
      rw [MonoidHom.pow_apply, ← det_heckeGen]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, hηval v hv.1, hSb v hv.2, Units.val_one]
  exact ⟨χ * (normChar (F := F))⁻¹, ⟨hηclass, hηcont, isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hpow⟩⟩,
    ⟨𝔣, h𝔣, hηmod⟩, E, hηval⟩

end DeterminantCharacter

end

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

namespace DeterminantCharacter

variable {F : Type} [Field F] [NumberField F]

private abbrev standardPins (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

private theorem mem_standardPins_Z (D : Set (AdelicGL2 (𝓞 F) F)) (x : (AdeleRing (𝓞 F) F)ˣ) : x ∈ (standardPins F D).Z :=
  Subgroup.mem_top x

private def toCentre (D : Set (AdelicGL2 (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ →* ↥(standardPins F D).Z where
  toFun x := ⟨x, mem_standardPins_Z D x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem solution_of_criterion (hcrit : TrivialityCriterion F) (D : Set (AdelicGL2 (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F (standardPins F D) Φ)
    (n : ℕ) (hn : 0 < n) (hbn : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Φ.b v ^ n = 1) :
    ∃ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar F η ∧
      (∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = Φ.b v := by
  obtain ⟨R, hR⟩ := hΦ
  have hRcont : Continuous R.toFun := hR
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero

  let χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := R.centralChar.comp (toCentre D)
  have hχ : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ((χ z : ℂˣ) : ℂ) = R.toFun (centralScalar (𝓞 F) F z * g₀) / R.toFun g₀ :=
    fun z => R.centralChar_apply_eq (toCentre D z) hg₀
  have hcont : Continuous χ := continuous_of_central_quotient R.toFun hRcont χ g₀ hχ
  have hclass : IsIdeleClassChar (𝓞 F) F χ :=
    isIdeleClassChar_of_left_invariant R.toFun χ g₀ hg₀ hχ fun γ g => R.left_invariant γ g
  have hmod : HeckeCharacter.AdmitsModulus F χ Φ.level :=
    admitsModulus_of_right_invariant Φ.level_ne_bot R.toFun χ g₀ hg₀ hχ fun g k hk => R.level_invariant g k hk
  have hval : ∀ v ∉ R.exceptionalSet,
      ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = (HeckeEigensystem.cNorm v)⁻¹ * Φ.b v := by
    intro v hv
    have h := R.centralChar_det_gen_eq_b hv (toCentre D (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))) rfl
    rw [HeckeEigensystem.toRawCentral_b] at h
    exact h
  exact exists_eta hcrit χ hcont hclass Φ.level_ne_bot hmod Φ.b R.exceptionalSet hval n hn hbn

end DeterminantCharacter

end

section IdeleCharacter

variable (F : Type) [Field F] [NumberField F]

private noncomputable def ideleChar_archIncl : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun z := (z, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

private theorem ideleChar_continuous_archIncl : Continuous (ideleChar_archIncl F) :=
  (continuous_id.prodMk continuous_const :
    Continuous fun z : InfiniteAdeleRing F =>
      ((z, (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

private noncomputable def ideleChar_component (v : HeightOneSpectrum (𝓞 F)) :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (finAdeleEval (𝓞 F) F v)

private noncomputable def ideleChar_archInv : InfiniteAdeleRing F → InfiniteAdeleRing F :=
  fun z w => (z w)⁻¹

private noncomputable def ideleChar_ball (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (n : ℕ) :
    Set (v.adicCompletion F) :=
  {b | Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)}

variable {F}

private theorem ideleChar_fin_apply_ne_zero (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (u : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) u.mul_inv)

private theorem ideleChar_idele_decomp (u : (AdeleRing (𝓞 F) F)ˣ) :
    u = Units.map (ideleChar_archIncl F) (Units.map (adeleArch (𝓞 F) F) u) *
        Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) u) :=
  Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)

private theorem ideleChar_component_apply (v : HeightOneSpectrum (𝓞 F)) (y : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (ideleChar_component F v y : v.adicCompletion F) = (y : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem ideleChar_component_localUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ideleChar_component F v (localUnit (𝓞 F) F v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

private theorem ideleChar_component_localUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (t : (w.adicCompletion F)ˣ) : ideleChar_component F v (localUnit (𝓞 F) F w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

omit [NumberField F] in
private theorem ideleChar_arch_apply_ne_zero (z : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (z : InfiniteAdeleRing F) w ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_arch_val_inv (z : (InfiniteAdeleRing F)ˣ) :
    ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = ideleChar_archInv F (z : InfiniteAdeleRing F) :=
  funext fun w => eq_inv_of_mul_eq_one_right
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_continuousAt_archInv (p : InfiniteAdeleRing F) (hp : ∀ w, p w ≠ 0) :
    ContinuousAt (ideleChar_archInv F) p :=
  continuousAt_pi.mpr fun w => (continuousAt_inv₀ (hp w)).comp (continuousAt_apply w p)

private theorem ideleChar_valued_ne_zero {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F} (ha : a ≠ 0) :
    Valued.v a ≠ 0 :=
  (map_ne_zero (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha

private theorem ideleChar_finite_supp {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 F) | HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0}.Finite :=
  (Ideal.finite_factors (show 𝔣 ≠ 0 from h𝔣)).subset fun v hv =>
    (Associates.count_ne_zero_iff_dvd (show 𝔣 ≠ 0 from h𝔣) v.irreducible).mp hv

private theorem ideleChar_ball_mem_nhds (v : HeightOneSpectrum (𝓞 F)) {a : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) : ideleChar_ball F v a n ∈ nhds a := by
  have ht : (uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (uniformizerUnit F v).ne_zero) ha
  have hopen : IsOpen (ideleChar_ball F v a n) :=
    (isOpen_setOf_valued_le v _ ht).preimage (continuous_id.sub continuous_const)
  refine hopen.mem_nhds ?_
  show Valued.v (a - a) ≤ _
  rw [sub_self, map_zero]
  exact zero_le'

private theorem ideleChar_congruence {v : HeightOneSpectrum (𝓞 F)} {a b : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) (hb : b ∈ ideleChar_ball F v a n) :
    Valued.v (a * b⁻¹) = 1 ∧ Valued.v (a * b⁻¹ - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  change Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a) at hb
  have ha0 : Valued.v a ≠ 0 := ideleChar_valued_ne_zero ha
  obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = Valued.v a := ⟨_, WithZero.exp_log ha0⟩
  have ht : Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)
      = WithZero.exp (m - (n + 1 : ℤ)) := by
    rw [map_mul, map_pow, valued_uniformizerUnit, ← hm, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [ht] at hb
  have hlt : Valued.v (b - a) < Valued.v a := by
    rw [← hm]
    exact hb.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have hba : Valued.v b = Valued.v a := Valuation.map_eq_of_sub_lt _ hlt
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hba
    exact ha0 hba.symm
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_inv₀, hba, mul_inv_cancel₀ ha0]
  · have h2 : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hb0]
    rw [h2, map_mul, map_inv₀, hba, Valuation.map_sub_swap, ← hm]
    calc Valued.v (b - a) * (WithZero.exp m)⁻¹
        ≤ WithZero.exp (m - (n + 1 : ℤ)) * (WithZero.exp m)⁻¹ := mul_le_mul_left hb _
      _ = WithZero.exp (-(n + 1 : ℤ)) := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]
          congr 1
          ring
      _ ≤ WithZero.exp (-(n : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

private theorem ideleChar_finIncl_eq_one (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 F)}
    (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v ∉ S, θ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))) = 1)
    (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
        Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v - 1)
          ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ))) :
    θ (Units.map (finIncl (𝓞 F) F) y) = 1 := by
  obtain ⟨hne, hcof⟩ := IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp y.isUnit
  have hZ : {v : HeightOneSpectrum (𝓞 F) | Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  have hv0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 :=
    fun v => ideleChar_valued_ne_zero (hne v)
  obtain ⟨k, hk⟩ : ∃ k : HeightOneSpectrum (𝓞 F) → ℤ,
      ∀ v, WithZero.exp (k v) = Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) :=
    ⟨fun v => WithZero.log _, fun v => WithZero.exp_log (hv0 v)⟩
  have hZS : ∀ v ∈ hZ.toFinset, v ∉ S := by
    intro v hv hvS
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    exact hv (hy v (Or.inl hvS)).1
  have hnotZ : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 →
      v ∉ hZ.toFinset := by
    intro v h1 hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    exact hv h1

  obtain ⟨c, hc⟩ : ∃ c : (FiniteAdeleRing (𝓞 F) F)ˣ,
      c = ∏ v ∈ hZ.toFinset, localUnit (𝓞 F) F v (uniformizerUnit F v ^ (-(k v))) := ⟨_, rfl⟩
  have hθc : θ (Units.map (finIncl (𝓞 F) F) c) = 1 := by
    rw [hc, map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_zpow, hS v (hZS v hv), _root_.one_zpow]
  have hevc_in : ∀ v ∈ hZ.toFinset, ideleChar_component F v c = uniformizerUnit F v ^ (-(k v)) := by
    intro v hv
    rw [hc, map_prod, Finset.prod_eq_single v]
    · exact ideleChar_component_localUnit_self v _
    · intro w _ hwv
      exact ideleChar_component_localUnit_of_ne (Ne.symm hwv) _
    · intro h
      exact absurd hv h
  have hevc_out : ∀ v, v ∉ hZ.toFinset → ideleChar_component F v c = 1 := by
    intro v hv
    rw [hc, map_prod]
    refine Finset.prod_eq_one fun w hw => ?_
    refine ideleChar_component_localUnit_of_ne (fun hvw => hv ?_) _
    rw [hvw]
    exact hw

  obtain ⟨u, hu⟩ : ∃ u : (FiniteAdeleRing (𝓞 F) F)ˣ, u = y * c⁻¹ := ⟨_, rfl⟩
  have hyu : y = u * c := by
    rw [hu]
    simp
  have hu_out : ∀ v, v ∉ hZ.toFinset →
      (u : FiniteAdeleRing (𝓞 F) F) v = (y : FiniteAdeleRing (𝓞 F) F) v := by
    intro v hv
    change (ideleChar_component F v u : v.adicCompletion F) = ideleChar_component F v y
    rw [hu, map_mul, map_inv, hevc_out v hv, inv_one, mul_one]
  have hu_val : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    intro v
    by_cases hv : v ∈ hZ.toFinset
    · change Valued.v (ideleChar_component F v u : v.adicCompletion F) = 1
      rw [hu, map_mul, map_inv, hevc_in v hv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, valued_uniformizerUnit, ideleChar_component_apply,
        ← hk v, ← WithZero.exp_zsmul]
      have h1 : (-(k v)) • (-1 : ℤ) = k v := by simp
      rw [h1]
      exact mul_inv_cancel₀ WithZero.exp_ne_zero
    · rw [hu_out v hv]
      by_contra h
      exact hv (by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact h)
  have hu_cong : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
    intro v
    by_cases hn : HeckeCharacter.idealMultiplicity F v 𝔣 = 0
    · rw [hn, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (Valuation.map_sub Valued.v _ _).trans (max_le (hu_val v).le (map_one Valued.v).le)
    · have hvZ : v ∉ hZ.toFinset := hnotZ v (hy v (Or.inr hn)).1
      rw [hu_out v hvZ]
      exact (hy v (Or.inr hn)).2
  have hθu : θ (Units.map (finIncl (𝓞 F) F) u) = 1 :=
    hmod (Units.map (finIncl (𝓞 F) F) u) rfl fun v => ⟨hu_val v, hu_cong v⟩
  rw [hyu, map_mul, map_mul, hθu, hθc, one_mul]

private theorem ideleChar_eq_one_of_denseRange (F : Type) [Field F] [NumberField F]
    (hwa : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      DenseRange (fun x : F =>
        ((fun v : S => algebraMap F (v.1.adicCompletion F) x),
         (fun w : NumberField.InfinitePlace F => algebraMap F w.Completion x))))
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 := by
  classical
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]

  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), T = S ∪ (ideleChar_finite_supp h𝔣).toFinset :=
    ⟨_, rfl⟩
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      v ∈ T := by
    intro v hv
    rw [hT, Finset.mem_union]
    rcases hv with h | h
    · exact Or.inl h
    · right
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact h

  have hx2 : ∀ v : HeightOneSpectrum (𝓞 F), (x : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
    ideleChar_fin_apply_ne_zero x
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : (InfiniteAdeleRing F)ˣ, x₁ = Units.map (adeleArch (𝓞 F) F) x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (InfiniteAdeleRing F)ˣ → ℂˣ,
      ∀ z, ψ z = θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) :=
    ⟨fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)), fun _ => rfl⟩
  have hψ_cont : Continuous ψ := by
    have hψ' : ψ = fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) := funext hψ
    rw [hψ']
    exact (hcont.comp (Continuous.units_map _ (ideleChar_continuous_archIncl F))).comp
      (continuous_const.mul continuous_inv)
  have hψ_one : ψ x₁ = 1 := by
    rw [hψ]
    simp

  have hstepA : ∀ N ∈ nhds (x₁ : InfiniteAdeleRing F),
      ∃ z : (InfiniteAdeleRing F)ˣ, (z : InfiniteAdeleRing F) ∈ N ∧ θ x = ψ z := by
    intro N hN
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨E, hE⟩ : ∃ E : Set (InfiniteAdeleRing F), E = archEval F w₀ ⁻¹' {c | c ≠ 0} := ⟨_, rfl⟩
    have hEN : E ∈ nhds (x₁ : InfiniteAdeleRing F) := by
      rw [hE]
      exact ((isOpen_ne (x := (0 : w₀.Completion))).preimage (continuous_archEval F w₀)).mem_nhds
        (ideleChar_arch_apply_ne_zero x₁ w₀)
    have hN' : N ∩ E ∈ nhds (x₁ : InfiniteAdeleRing F) := Filter.inter_mem hN hEN
    have hpi : Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))
        ∈ nhds (fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1) :=
      set_pi_mem_nhds Set.finite_univ fun v _ => ideleChar_ball_mem_nhds v.1 (hx2 v.1) _
    obtain ⟨pt, hpt_def⟩ : ∃ pt : ((v : T) → v.1.adicCompletion F) × InfiniteAdeleRing F,
        pt = ((fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1), (x₁ : InfiniteAdeleRing F)) := ⟨_, rfl⟩
    have hU : (Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))) ×ˢ (N ∩ E) ∈ nhds pt := by
      rw [hpt_def, nhds_prod_eq]
      exact Filter.prod_mem_prod hpi hN'
    have hpt := hwa T pt
    obtain ⟨q, hqU, α, hαq⟩ := mem_closure_iff_nhds.mp hpt _ hU
    subst hαq
    have hfin : ∀ v : T, algebraMap F (v.1.adicCompletion F) α ∈ ideleChar_ball F v.1
        ((x : AdeleRing (𝓞 F) F).2 v.1) (HeckeCharacter.idealMultiplicity F v.1 𝔣) :=
      fun v => (Set.mem_univ_pi.mp hqU.1) v
    have harch : (algebraMap F (AdeleRing (𝓞 F) F) α).1 ∈ N ∩ E := hqU.2
    have hα0 : α ≠ 0 := by
      intro h
      have h2 := harch.2
      rw [hE, Set.mem_preimage, Set.mem_setOf_eq, archEval_apply] at h2
      subst h
      exact h2 (map_zero (algebraMap F w₀.Completion))

    obtain ⟨P, hP⟩ : ∃ P : (AdeleRing (𝓞 F) F)ˣ,
        P = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) (Units.mk0 α hα0) := ⟨_, rfl⟩
    have hθP : θ P = 1 := by
      rw [hP]
      exact hclass _
    have hcomp : ∀ v : HeightOneSpectrum (𝓞 F),
        ((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
          = (x : AdeleRing (𝓞 F) F).2 v * (algebraMap F (v.adicCompletion F) α)⁻¹ := by
      intro v
      rw [hP, ← map_inv₀]
      rfl
    have hyf : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
        Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
          Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v - 1)
            ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
      intro v hv
      have hb : algebraMap F (v.adicCompletion F) α ∈ ideleChar_ball F v ((x : AdeleRing (𝓞 F) F).2 v)
          (HeckeCharacter.idealMultiplicity F v 𝔣) := hfin ⟨v, hmemT v hv⟩
      rw [hcomp v]
      exact ideleChar_congruence (hx2 v) _ hb
    have hθfin : θ (Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) (x * P⁻¹))) = 1 :=
      ideleChar_finIncl_eq_one θ hmod hS _ hyf

    refine ⟨Units.map (adeleArch (𝓞 F) F) P, ?_, ?_⟩
    · rw [hP]
      exact harch.1
    · have h1 : θ x = θ (x * P⁻¹) := by
        rw [map_mul, map_inv, hθP, inv_one, mul_one]
      have h3 : Units.map (adeleArch (𝓞 F) F) (x * P⁻¹) = x₁ * (Units.map (adeleArch (𝓞 F) F) P)⁻¹ := by
        rw [map_mul, map_inv, hx₁]
      rw [h1, ideleChar_idele_decomp (x * P⁻¹), map_mul, hθfin, mul_one, hψ, h3]

  refine Specializes.eq ?_
  rw [specializes_iff_forall_open]
  intro V hV h1V
  have hVψ : ψ ⁻¹' V ∈ nhds x₁ :=
    hψ_cont.continuousAt.preimage_mem_nhds (by rw [hψ_one]; exact hV.mem_nhds h1V)
  rw [(Units.isEmbedding_embedProduct (M := InfiniteAdeleRing F)).toIsInducing.nhds_eq_comap x₁,
    Filter.mem_comap] at hVψ
  obtain ⟨Q, hQ, hQsub⟩ := hVψ
  change Q ∈ nhds ((x₁ : InfiniteAdeleRing F),
    MulOpposite.op ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) at hQ
  rw [mem_nhds_prod_iff] at hQ
  obtain ⟨A, hA, B', hB', hAB⟩ := hQ
  have hB : MulOpposite.op ⁻¹' B' ∈ nhds ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB'
  rw [ideleChar_arch_val_inv x₁] at hB
  have hB2 : ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B') ∈ nhds (x₁ : InfiniteAdeleRing F) :=
    (ideleChar_continuousAt_archInv (x₁ : InfiniteAdeleRing F) (ideleChar_arch_apply_ne_zero x₁)).preimage_mem_nhds hB
  obtain ⟨z, hz, hθz⟩ := hstepA (A ∩ ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B')) (Filter.inter_mem hA hB2)
  have hz2 : MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) ∈ B' := by
    rw [ideleChar_arch_val_inv z]
    exact hz.2
  have hzQ : z ∈ Units.embedProduct (InfiniteAdeleRing F) ⁻¹' Q := by
    change ((z : InfiniteAdeleRing F),
      MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) ∈ Q
    exact hAB (Set.mk_mem_prod hz.1 hz2)
  rw [hθz]
  exact hQsub hzQ

private theorem ideleChar_eq_one (F : Type) [Field F] [NumberField F]
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 :=
  ideleChar_eq_one_of_denseRange F NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
    θ hcont hclass 𝔣 h𝔣 hmod S hS

end IdeleCharacter

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ)
    (n : ℕ) (hn : 0 < n) (hbn : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Φ.b v ^ n = 1) :
    ∃ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar F η ∧
      (∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = Φ.b v :=
  DeterminantCharacter.solution_of_criterion (ideleChar_eq_one F) D Φ hΦ n hn hbn

#print axioms solution

end S_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable (solution)
