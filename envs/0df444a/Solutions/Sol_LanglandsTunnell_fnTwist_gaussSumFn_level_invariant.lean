-- Prove2me | solution 1 for LanglandsTunnell.fnTwist_gaussSumFn_level_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b38ef745-07a1-5629-bfc9-6d83a691b2f2

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant

set_option Elab.async false

open NumberField AutomorphicForm

section M4aP7_LevelMono
noncomputable section
open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam
open AutomorphicForm.SmoothCusp

namespace P7LevelMono

section Rebase

variable {G : Type*} [Group G]

end Rebase

section Antitone

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem idealBound_mono {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N' v ≤ idealBound R N v := by
  classical
  have hN : N ≠ ⊥ := fun h => hN' (le_bot_iff.mp (h ▸ hle))
  rw [idealBound_of_ne_bot hN', idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff,
    Nat.cast_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hN')
    (Associates.irreducible_mk.mpr v.irreducible)
    (Associates.mk_le_mk_of_dvd (Ideal.dvd_iff_le.mpr hle))

private theorem idealBall_mono {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥) :
    idealBall R K N' ⊆ idealBall R K N := fun _ hx v => (hx v).trans (idealBound_mono hle hN' v)

end Antitone

section Key

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem finComponent_glFin_heckeGenAt_of_ne (v : HeightOneSpectrum R) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    finComponent R K w (glFin R K (heckeGenAt R K v t)) = 1 := by
  ext i j
  rw [finComponent_apply, glFin_apply, heckeGenAt_snd_apply_of_ne t hw, Units.val_one]

end Key

section Transport

variable (F : Type) [Field F] [NumberField F]

end Transport

section HU

variable (F : Type) [Field F] [NumberField F]

private theorem det_fst_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have h2 := Matrix.GeneralLinearGroup.map_det (n := Fin 2) (adeleArch (𝓞 F) F) u
  have h1 : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (adeleArch (𝓞 F) F) u) = 1 := by
    show Matrix.GeneralLinearGroup.det (glArch (𝓞 F) F u) = 1
    rw [hu, map_one]
  rw [h2] at h1
  have h3 := congrArg (fun z : (InfiniteAdeleRing F)ˣ => (z : InfiniteAdeleRing F)) h1
  simpa [Units.coe_map, adeleArch_apply] using h3

private theorem valued_det_snd_eq_one {M : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F M) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
      = 1 := by
  have hfin : ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
      = ((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u) : (FiniteAdeleRing (𝓞 F) F)ˣ)
          : FiniteAdeleRing (𝓞 F) F) := by
    have h := Matrix.GeneralLinearGroup.map_det (n := Fin 2) (adeleFin (𝓞 F) F) u
    have h' := congrArg (fun z : (FiniteAdeleRing (𝓞 F) F)ˣ => (z : FiniteAdeleRing (𝓞 F) F)) h
    simp only [Units.coe_map, MonoidHom.coe_coe, adeleFin_apply] at h'
    exact h'.symm
  rw [hfin]
  have hint : ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F),
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        ∈ integralFiniteAdeles (𝓞 F) F) →
      ((Matrix.GeneralLinearGroup.det g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
        ∈ integralFiniteAdeles (𝓞 F) F := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hg 0 0) (hg 1 1))
      (mul_mem_integralFiniteAdeles (hg 0 1) (hg 1 0))
  have h1 : Valued.v (((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u)
      : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 :=
    valued_apply_le_one (hint _ hu.1.integral) v
  have h2 : Valued.v ((((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u))⁻¹
      : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := by
    rw [← map_inv]
    exact valued_apply_le_one (hint _ hu.2.integral) v
  have hmul : Valued.v (((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u)
        : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v)
      * Valued.v ((((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u))⁻¹
        : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, coe_one_apply,
      map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = _ := hmul.symm
    _ ≤ Valued.v (((Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F u)
          : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) * 1 :=
        mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end HU

section ArchTrim

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem matrix_eq_of_parts {M M' : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (ha : (adeleArch R K).mapMatrix M = (adeleArch R K).mapMatrix M')
    (hf : (adeleFin R K).mapMatrix M = (adeleFin R K).mapMatrix M') : M = M' := by
  ext i j
  exact Prod.ext (congrFun (congrFun ha i) j) (congrFun (congrFun hf i) j)

end ArchTrim

section ArchTrimProduction

variable (F : Type) [Field F] [NumberField F]

end ArchTrimProduction

section FinSurgery

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private def adeleOn (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨fun w => if w ∈ S then y w else 0,
    S.eventually_cofinite_notMem.mono fun w hw => by
      dsimp only
      rw [if_neg hw]
      exact (w.adicCompletionIntegers K).zero_mem⟩

private theorem adeleOn_apply (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) (w : HeightOneSpectrum R) :
    adeleOn S y w = if w ∈ S then y w else 0 := rfl

private theorem adeleOn_apply_of_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) {w : HeightOneSpectrum R} (hw : w ∈ S) :
    adeleOn S y w = y w := by
  rw [adeleOn_apply, if_pos hw]

private theorem adeleOn_apply_of_not_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ∉ S) : adeleOn S y w = 0 := by
  rw [adeleOn_apply, if_neg hw]

private def finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j =>
    (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, m i j) : AdeleRing R K)

private theorem mapMatrix_adeleArch_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleArch R K).mapMatrix (finPair m) = 1 := by
  ext i j
  rfl

private theorem mapMatrix_adeleFin_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleFin R K).mapMatrix (finPair m) = m := by
  ext i j
  rfl

private theorem finPair_one : finPair (R := R) (K := K) 1 = 1 :=
  matrix_eq_of_parts (by rw [mapMatrix_adeleArch_finPair, map_one])
    (by rw [mapMatrix_adeleFin_finPair, map_one])

private theorem finPair_mul (m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finPair m * finPair m' = finPair (m * m') :=
  matrix_eq_of_parts
    (by rw [map_mul, mapMatrix_adeleArch_finPair, mapMatrix_adeleArch_finPair,
      mapMatrix_adeleArch_finPair, mul_one])
    (by rw [map_mul, mapMatrix_adeleFin_finPair, mapMatrix_adeleFin_finPair,
      mapMatrix_adeleFin_finPair])

private def finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (AdeleRing R K) where
  val := finPair (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  inv := finPair
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  val_inv := by rw [finPair_mul, Units.mul_inv, finPair_one]
  inv_val := by rw [finPair_mul, Units.inv_mul, finPair_one]

private theorem glArch_finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : glArch R K (finLift g) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

private theorem glFin_finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : glFin R K (finLift g) = g := by
  ext i j
  rfl

end FinSurgery

section FinSurgeryProduction

variable (F : Type) [Field F] [NumberField F]

end FinSurgeryProduction

end P7LevelMono

section Prints
end Prints

end
end M4aP7_LevelMono

section M4aP7_LevelMonoFurniture
noncomputable section
open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam

namespace P7LevelMono

section Generic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem unipotentGL2_inv_coe {A : Type*} [CommRing A] (y : A) :
    (((unipotentGL2 y)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, -y; 0, 1] := rfl

private theorem unipotent_conj_coe {A : Type*} [CommRing A] (k : GL (Fin 2) A) (y y' : A) :
    (((unipotentGL2 y')⁻¹ * k * unipotentGL2 y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = !![(k : Matrix (Fin 2) (Fin 2) A) 0 0 - y' * (k : Matrix (Fin 2) (Fin 2) A) 1 0,
            ((k : Matrix (Fin 2) (Fin 2) A) 0 0 * y + (k : Matrix (Fin 2) (Fin 2) A) 0 1)
              - y' * ((k : Matrix (Fin 2) (Fin 2) A) 1 0 * y + (k : Matrix (Fin 2) (Fin 2) A) 1 1);
          (k : Matrix (Fin 2) (Fin 2) A) 1 0,
            (k : Matrix (Fin 2) (Fin 2) A) 1 0 * y + (k : Matrix (Fin 2) (Fin 2) A) 1 1] := by
  ext i j
  rw [Units.val_mul, Units.val_mul, unipotentGL2_inv_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> ring

private theorem valued_mul_le_of_mem_idealBall {N' : Ideal R} {c y : FiniteAdeleRing R K}
    (hc : c ∈ idealBall R K N') (w : HeightOneSpectrum R) :
    Valued.v ((c * y) w) ≤ Valued.v (y w) * idealBound R N' w := by
  rw [coe_mul_apply, map_mul, mul_comm]
  exact mul_le_mul' le_rfl (hc w)

private theorem mul_mem_idealBall_of_bound {N N' : Ideal R} {c y : FiniteAdeleRing R K}
    (hc : c ∈ idealBall R K N')
    (hy : ∀ w, Valued.v (y w) * idealBound R N' w ≤ idealBound R N w) :
    c * y ∈ idealBall R K N := fun w =>
  (valued_mul_le_of_mem_idealBall hc w).trans (hy w)

private theorem mul_mem_integralFiniteAdeles_of_bound {N' : Ideal R} {c y : FiniteAdeleRing R K}
    (hc : c ∈ idealBall R K N') (hy : ∀ w, Valued.v (y w) * idealBound R N' w ≤ 1) :
    c * y ∈ integralFiniteAdeles R K := fun w =>
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
    ((valued_mul_le_of_mem_idealBall hc w).trans (hy w))

private theorem mul_mul_mem_integralFiniteAdeles_of_bound {N' : Ideal R} {c y y' : FiniteAdeleRing R K}
    (hc : c ∈ idealBall R K N')
    (hyy' : ∀ w, Valued.v (y' w) * Valued.v (y w) * idealBound R N' w ≤ 1) :
    y' * (c * y) ∈ integralFiniteAdeles R K := fun w =>
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    rw [coe_mul_apply, map_mul]
    calc Valued.v (y' w) * Valued.v ((c * y) w)
        ≤ Valued.v (y' w) * (Valued.v (y w) * idealBound R N' w) :=
          mul_le_mul' le_rfl (valued_mul_le_of_mem_idealBall hc w)
      _ = Valued.v (y' w) * Valued.v (y w) * idealBound R N' w := (mul_assoc _ _ _).symm
      _ ≤ 1 := hyy' w)

private theorem isLevelOneMatrix_unipotent_conj {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥)
    {k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (hk : IsLevelOneMatrix R K N' k)
    {y y' : FiniteAdeleRing R K}
    (hy : ∀ w, Valued.v (y w) * idealBound R N' w ≤ idealBound R N w)
    (hy' : ∀ w, Valued.v (y' w) * idealBound R N' w ≤ idealBound R N w)
    (hyy' : ∀ w, Valued.v (y' w) * Valued.v (y w) * idealBound R N' w ≤ 1)
    (hcomp : k 0 0 * y - y' * k 1 1 ∈ integralFiniteAdeles R K) :
    IsLevelOneMatrix R K N
      !![k 0 0 - y' * k 1 0, (k 0 0 * y + k 0 1) - y' * (k 1 0 * y + k 1 1);
        k 1 0, k 1 0 * y + k 1 1] := by
  have hy1 : ∀ w, Valued.v (y w) * idealBound R N' w ≤ 1 :=
    fun w => (hy w).trans (idealBound_le_one N w)
  have hy'1 : ∀ w, Valued.v (y' w) * idealBound R N' w ≤ 1 :=
    fun w => (hy' w).trans (idealBound_le_one N w)
  have hc : k 1 0 ∈ idealBall R K N' := hk.lowerLeft
  have hy'c : y' * k 1 0 ∈ integralFiniteAdeles R K := by
    rw [mul_comm]; exact mul_mem_integralFiniteAdeles_of_bound hc hy'1
  have hcy : k 1 0 * y ∈ integralFiniteAdeles R K := mul_mem_integralFiniteAdeles_of_bound hc hy1
  have hy'cy : y' * (k 1 0 * y) ∈ integralFiniteAdeles R K :=
    mul_mul_mem_integralFiniteAdeles_of_bound hc hyy'
  refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
  · intro i j
    fin_cases i <;> fin_cases j
    · exact sub_mem_integralFiniteAdeles (hk.integral 0 0) hy'c
    · have : (k 0 0 * y + k 0 1) - y' * (k 1 0 * y + k 1 1)
          = (k 0 0 * y - y' * k 1 1) + (k 0 1 - y' * (k 1 0 * y)) := by ring
      show (k 0 0 * y + k 0 1) - y' * (k 1 0 * y + k 1 1) ∈ integralFiniteAdeles R K
      rw [this]
      exact add_mem_integralFiniteAdeles hcomp (sub_mem_integralFiniteAdeles (hk.integral 0 1) hy'cy)
    · exact hk.integral 1 0
    · exact add_mem_integralFiniteAdeles hcy (hk.integral 1 1)
  · show k 1 0 ∈ idealBall R K N
    exact idealBall_mono hle hN' hc
  · show (k 1 0 * y + k 1 1) - 1 ∈ idealBall R K N
    have : (k 1 0 * y + k 1 1) - 1 = k 1 0 * y + (k 1 1 - 1) := by ring
    rw [this]
    exact add_mem_idealBall (mul_mem_idealBall_of_bound hc hy) (idealBall_mono hle hN' hk.lowerRight)

private theorem inv_comp_of_comp {N' : Ideal R} {k : GL (Fin 2) (FiniteAdeleRing R K)}
    (hk : k ∈ finiteLevelOne R K N') {y y' : FiniteAdeleRing R K}
    (hcomp : (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 * y
      - y' * (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 ∈ integralFiniteAdeles R K) :
    ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 * y'
      - y * ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1
      ∈ integralFiniteAdeles R K := by
  set A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hA
  set B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hB
  have hBA : B * A = 1 := by rw [hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have e00 := congrFun (congrFun hBA 0) 0
  have e01 := congrFun (congrFun hBA 0) 1
  have e10 := congrFun (congrFun hBA 1) 0
  have e11 := congrFun (congrFun hBA 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne h01] at e01
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne h10] at e10
  have key : B 0 0 * y' - y * B 1 1
      = -((B 0 0 * B 1 1 - B 0 1 * B 1 0) * (A 0 0 * y - y' * A 1 1)) := by
    linear_combination (-(y' * B 0 0)) * e11 + (y' * B 1 0) * e01 + (y * B 1 1) * e00
      - (y * B 0 1) * e10
  rw [key]
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 ∈ integralFiniteAdeles R K :=
    sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hk.2.integral 0 0) (hk.2.integral 1 1))
      (mul_mem_integralFiniteAdeles (hk.2.integral 0 1) (hk.2.integral 1 0))
  have hprod := mul_mem_integralFiniteAdeles hdet hcomp
  exact fun w => neg_mem (hprod w)

private theorem unipotent_conj_mem_finiteLevelOne {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥)
    {k : GL (Fin 2) (FiniteAdeleRing R K)} (hk : k ∈ finiteLevelOne R K N')
    {y y' : FiniteAdeleRing R K}
    (hy : ∀ w, Valued.v (y w) * idealBound R N' w ≤ idealBound R N w)
    (hy' : ∀ w, Valued.v (y' w) * idealBound R N' w ≤ idealBound R N w)
    (hyy' : ∀ w, Valued.v (y' w) * Valued.v (y w) * idealBound R N' w ≤ 1)
    (hcomp : (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 * y
      - y' * (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 ∈ integralFiniteAdeles R K) :
    (unipotentGL2 y')⁻¹ * k * unipotentGL2 y ∈ finiteLevelOne R K N := by
  refine ⟨?_, ?_⟩
  · rw [unipotent_conj_coe]
    exact isLevelOneMatrix_unipotent_conj hle hN' hk.1 hy hy' hyy' hcomp
  · have hinv : ((unipotentGL2 y')⁻¹ * k * unipotentGL2 y)⁻¹
        = (unipotentGL2 y)⁻¹ * k⁻¹ * unipotentGL2 y' := by group
    rw [hinv, unipotent_conj_coe]
    exact isLevelOneMatrix_unipotent_conj hle hN' hk.2 hy' hy
      (fun w => by rw [mul_comm (Valued.v (y w))]; exact hyy' w) (inv_comp_of_comp hk hcomp)

private theorem finLift_unipotent_conj_mem {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥)
    {k : GL (Fin 2) (AdeleRing R K)} (hk : k ∈ levelOne R K N' ⊓ (glArch R K).ker)
    {y y' : FiniteAdeleRing R K}
    (hy : ∀ w, Valued.v (y w) * idealBound R N' w ≤ idealBound R N w)
    (hy' : ∀ w, Valued.v (y' w) * idealBound R N' w ≤ idealBound R N w)
    (hyy' : ∀ w, Valued.v (y' w) * Valued.v (y w) * idealBound R N' w ≤ 1)
    (hcomp : (glFin R K k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 * y
      - y' * (glFin R K k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1
        ∈ integralFiniteAdeles R K) :
    (finLift (unipotentGL2 y'))⁻¹ * k * finLift (unipotentGL2 y)
      ∈ levelOne R K N ⊓ (glArch R K).ker := by
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
  rw [mem_levelOne_iff] at hk1
  rw [MonoidHom.mem_ker] at hk2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, map_mul, map_mul, map_inv, glFin_finLift, glFin_finLift]
    exact unipotent_conj_mem_finiteLevelOne hle hN' hk1 hy hy' hyy' hcomp
  · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, glArch_finLift, glArch_finLift, hk2, inv_one,
      one_mul, one_mul]

end Generic

section Production

variable (F : Type) [Field F] [NumberField F]

private theorem finLift_unipotent_conj_mem_productionPinsCompact_U {N N' : Ideal (𝓞 F)} (hle : N' ≤ N)
    (hN' : N' ≠ ⊥) {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ (productionPinsCompact F).U N')
    {y y' : FiniteAdeleRing (𝓞 F) F}
    (hy : ∀ w, Valued.v (y w) * idealBound (𝓞 F) N' w ≤ idealBound (𝓞 F) N w)
    (hy' : ∀ w, Valued.v (y' w) * idealBound (𝓞 F) N' w ≤ idealBound (𝓞 F) N w)
    (hyy' : ∀ w, Valued.v (y' w) * Valued.v (y w) * idealBound (𝓞 F) N' w ≤ 1)
    (hcomp : (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 * y
      - y' * (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1
        ∈ integralFiniteAdeles (𝓞 F) F) :
    (finLift (unipotentGL2 y'))⁻¹ * k * finLift (unipotentGL2 y) ∈ (productionPinsCompact F).U N := by
  rw [productionPinsCompact_U] at hk ⊢
  exact finLift_unipotent_conj_mem hle hN' hk hy hy' hyy' hcomp

end Production

end P7LevelMono

section Prints
end Prints

end
end M4aP7_LevelMonoFurniture

section M4aP7_LevelMonoFurniture2
set_option maxSynthPendingDepth 3

noncomputable section
open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam

namespace P7LevelMono

section LocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

private theorem units_map_quotient_maximalIdeal_pow_surjective (n : ℕ) :
    Function.Surjective
      (Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hsub : Subsingleton (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [hn, pow_zero, Ideal.one_eq_top])
    exact fun y => ⟨1, Subsingleton.elim _ _⟩
  · refine IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective ?_
    refine isLocalHom_of_le_jacobson_bot _ ?_
    calc (IsLocalRing.maximalIdeal A) ^ n
        ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self hn.ne'
      _ = Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

private def unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : Aˣ :=
  Function.surjInv (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem unitQuotLift_spec (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom
      (unitQuotLift A n x) = x :=
  Function.surjInv_eq (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem mk_coe_unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) (unitQuotLift A n x : A)
      = ((x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
  congrArg Units.val (unitQuotLift_spec A n x)

end LocalRing

section IdealBound

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private theorem idealBound_lt_one_of_dvd {N : Ideal R} (hN : N ≠ ⊥) {w : HeightOneSpectrum R}
    (hw : w.asIdeal ∣ N) : idealBound R N w < 1 := by
  classical
  rw [idealBound_of_ne_bot hN, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have h0 : (Associates.mk w.asIdeal).count (Associates.mk N).factors ≠ 0 :=
    (Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) w.irreducible).mpr hw
  omega

private theorem idealBound_mul {N M : Ideal R} (hN : N ≠ ⊥) (hM : M ≠ ⊥) (w : HeightOneSpectrum R) :
    idealBound R (N * M) w = idealBound R N w * idealBound R M w := by
  classical
  have hNM : N * M ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hN hM
  rw [idealBound_of_ne_bot hNM, idealBound_of_ne_bot hN, idealBound_of_ne_bot hM,
    ← WithZero.exp_add, ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr (show N ≠ 0 from hN))
      (Associates.mk_ne_zero.mpr (show M ≠ 0 from hM)) w.associates_irreducible]
  congr 1; push_cast; ring

private theorem idealBound_mul_le_right {N M : Ideal R} (hN : N ≠ ⊥) (hM : M ≠ ⊥)
    (w : HeightOneSpectrum R) : idealBound R (N * M) w ≤ idealBound R M w := by
  rw [idealBound_mul hN hM]
  exact mul_le_of_le_one_left' (idealBound_le_one N w)

private theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨WithZero.log γ, (WithZero.exp_log h0).symm⟩
    subst hm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.mpr (by omega)

end IdealBound

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

private def localUnif : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_localUnif : Valued.v (localUnif K v) = WithZero.exp (-1 : ℤ) := by
  unfold localUnif
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem valued_localUnif_inv_pow (n : ℕ) :
    Valued.v ((localUnif K v)⁻¹ ^ n) = WithZero.exp (n : ℤ) := by
  rw [map_pow, map_inv₀, valued_localUnif, ← WithZero.exp_neg, neg_neg]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, WithZero.exp_add]

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) :=
  Valuation.valuationSubring.integers _

private theorem valued_coe_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (integers_adicCompletionIntegers K v).one_of_isUnit hx

private theorem isUnit_of_valued_coe_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1) : IsUnit x :=
  (integers_adicCompletionIntegers K v).isUnit_of_one' hx

private theorem valued_units_coe (r : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (((r : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 :=
  valued_coe_eq_one_of_isUnit K v r.isUnit

private def unitOfValuedEqOne (a : v.adicCompletion K) (ha : Valued.v a = 1) :
    (v.adicCompletionIntegers K)ˣ :=
  (isUnit_of_valued_coe_eq_one K v
    (x := ⟨a, (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mpr ha.le⟩) ha).unit

private theorem coe_coe_unitOfValuedEqOne (a : v.adicCompletion K) (ha : Valued.v a = 1) :
    ((unitOfValuedEqOne K v a ha : v.adicCompletionIntegers K) : v.adicCompletion K) = a :=
  rfl

private theorem valued_coe_le_exp_neg_one_of_mem_maximalIdeal {x : v.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  refine le_exp_neg_one_of_lt_one (lt_of_le_of_ne
    ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2) fun h => ?_)
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx))
    (isUnit_of_valued_coe_eq_one K v h)

private theorem valued_coe_le_exp_neg_of_mem_maximalIdeal_pow {n : ℕ} {x : v.adicCompletionIntegers K}
    (hx : x ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      ≤ WithZero.exp (-(n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  | succ n ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun m hm y hy => ?_) (fun y z hy hz => ?_)
      · rw [show ((m * y : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (m : v.adicCompletion K) * y from rfl, map_mul, Nat.cast_succ, neg_add,
          WithZero.exp_add]
        exact mul_le_mul' (ih hm) (valued_coe_le_exp_neg_one_of_mem_maximalIdeal K v hy)
      · rw [show ((y + z : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (y : v.adicCompletion K) + z from rfl]
        exact Valuation.map_add_le _ hy hz

private theorem valued_units_coe_mul_localUnif_inv_pow (r : (v.adicCompletionIntegers K)ˣ) (n : ℕ) :
    Valued.v ((((r : v.adicCompletionIntegers K) : v.adicCompletion K)) * (localUnif K v)⁻¹ ^ n)
      = WithZero.exp (n : ℤ) := by
  rw [map_mul, valued_units_coe, one_mul, valued_localUnif_inv_pow]

private theorem valued_compat_le_one_core (n : ℕ) {α ρ ρ' d : v.adicCompletion K}
    (hρ' : Valued.v ρ' = 1)
    (h1 : Valued.v (α * ρ - ρ') ≤ WithZero.exp (-(n : ℤ)))
    (hd : Valued.v (d - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (α * (ρ * (localUnif K v)⁻¹ ^ n) - (ρ' * (localUnif K v)⁻¹ ^ n) * d) ≤ 1 := by
  have key : α * (ρ * (localUnif K v)⁻¹ ^ n) - (ρ' * (localUnif K v)⁻¹ ^ n) * d
      = (localUnif K v)⁻¹ ^ n * ((α * ρ - ρ') - ρ' * (d - 1)) := by ring
  have h2 : Valued.v (ρ' * (d - 1)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [map_mul, hρ', one_mul]; exact hd
  rw [key, map_mul, valued_localUnif_inv_pow]
  calc WithZero.exp (n : ℤ) * Valued.v ((α * ρ - ρ') - ρ' * (d - 1))
      ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul_right (Valuation.map_sub_le _ h1 h2) _
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

private theorem valued_det_mul_div_sub_one_le_core (n : ℕ) {α ρ ρ' det : v.adicCompletion K}
    (hρ : Valued.v ρ = 1) (hρ' : Valued.v ρ' = 1)
    (h1 : Valued.v (α * ρ - ρ') ≤ WithZero.exp (-(n : ℤ)))
    (hdet : Valued.v (det - α) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (det * ρ * ρ'⁻¹ - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hρ'0 : ρ' ≠ 0 := fun h => by rw [h, map_zero] at hρ'; exact zero_ne_one hρ'
  have key : det * ρ * ρ'⁻¹ - 1 = ρ'⁻¹ * ((det - α) * ρ + (α * ρ - ρ')) := by
    field_simp
    ring
  have h2 : Valued.v ((det - α) * ρ) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [map_mul, hρ, mul_one]; exact hdet
  rw [key, map_mul, map_inv₀, hρ', inv_one, one_mul]
  exact Valuation.map_add_le _ h2 h1

private theorem valued_coe_mul_coe_sub_coe_le (n : ℕ) (aInt r r' : (v.adicCompletionIntegers K)ˣ)
    (hr' : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (r' : v.adicCompletionIntegers K)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        ((aInt : v.adicCompletionIntegers K) * r)) :
    Valued.v ((((aInt : v.adicCompletionIntegers K) : v.adicCompletion K))
        * (((r : v.adicCompletionIntegers K) : v.adicCompletion K))
      - (((r' : v.adicCompletionIntegers K) : v.adicCompletion K)))
      ≤ WithZero.exp (-(n : ℤ)) := by
  have h := valued_coe_le_exp_neg_of_mem_maximalIdeal_pow K v (Ideal.Quotient.eq.mp hr'.symm)
  rwa [AddSubgroupClass.coe_sub, MulMemClass.coe_mul] at h

private theorem valued_compat_le_one (n : ℕ) (aInt : (v.adicCompletionIntegers K)ˣ)
    {a : v.adicCompletion K}
    (ha : a = (((aInt : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)
      : v.adicCompletion K))
    (r r' : (v.adicCompletionIntegers K)ˣ)
    (hr' : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (r' : v.adicCompletionIntegers K)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        ((aInt : v.adicCompletionIntegers K) * r))
    {d : v.adicCompletion K} (hd : Valued.v (d - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (a * ((((r : v.adicCompletionIntegers K) : v.adicCompletion K))
          * (localUnif K v)⁻¹ ^ n)
      - ((((r' : v.adicCompletionIntegers K) : v.adicCompletion K)) * (localUnif K v)⁻¹ ^ n)
          * d) ≤ 1 := by
  subst ha
  exact valued_compat_le_one_core K v n (valued_units_coe K v r')
    (valued_coe_mul_coe_sub_coe_le K v n aInt r r' hr') hd

private theorem valued_det_mul_div_sub_one_le (n : ℕ) (aInt : (v.adicCompletionIntegers K)ˣ)
    {a : v.adicCompletion K}
    (ha : a = (((aInt : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)
      : v.adicCompletion K))
    (r r' : (v.adicCompletionIntegers K)ˣ)
    (hr' : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (r' : v.adicCompletionIntegers K)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        ((aInt : v.adicCompletionIntegers K) * r))
    {det : v.adicCompletion K} (hdet : Valued.v (det - a) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (det * (((r : v.adicCompletionIntegers K) : v.adicCompletion K))
        * (((r' : v.adicCompletionIntegers K) : v.adicCompletion K))⁻¹ - 1)
      ≤ WithZero.exp (-(n : ℤ)) := by
  subst ha
  exact valued_det_mul_div_sub_one_le_core K v n (valued_units_coe K v r) (valued_units_coe K v r')
    (valued_coe_mul_coe_sub_coe_le K v n aInt r r' hr') hdet

private theorem valued_det_apply_eq_one {N : Ideal R} {k : GL (Fin 2) (FiniteAdeleRing R K)}
    (hk : k ∈ finiteLevelOne R K N) (w : HeightOneSpectrum R) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w) = 1 := by
  have hint : ∀ {g : GL (Fin 2) (FiniteAdeleRing R K)},
      IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) →
      (Matrix.GeneralLinearGroup.det g : FiniteAdeleRing R K) ∈ integralFiniteAdeles R K := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hg.integral 0 0)
      (hg.integral 1 1)) (mul_mem_integralFiniteAdeles (hg.integral 0 1) (hg.integral 1 0))
  have h1 : Valued.v ((Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers R K w).mp (hint hk.1 w)
  have h2 : Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : FiniteAdeleRing R K) w) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers R K w).mp (hint hk.2 w)
  have hprod : (Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w
      * (Matrix.GeneralLinearGroup.det k⁻¹ : FiniteAdeleRing R K) w = 1 := by
    rw [← coe_mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      coe_one_apply]
  refine le_antisymm h1 ?_
  have hv : Valued.v ((Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w)
      * Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : FiniteAdeleRing R K) w) = 1 := by
    rw [← map_mul, hprod, map_one]
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w)
          * Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : FiniteAdeleRing R K) w) := hv.symm
    _ ≤ Valued.v ((Matrix.GeneralLinearGroup.det k : FiniteAdeleRing R K) w) * 1 :=
        mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem valued_det_sub_apply_zero_zero_le {N : Ideal R}
    {k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (hk : IsLevelOneMatrix R K N k)
    (w : HeightOneSpectrum R) :
    Valued.v ((k.det - k 0 0) w) ≤ idealBound R N w := by
  rw [Matrix.det_fin_two,
    show (k 0 0 * k 1 1 - k 0 1 * k 1 0 - k 0 0) w = k 0 0 w * (k 1 1 - 1) w - k 0 1 w * k 1 0 w by
      rw [coe_sub_apply, coe_sub_apply, coe_mul_apply, coe_mul_apply, coe_sub_apply,
        coe_one_apply]; ring]
  refine Valuation.map_sub_le _ ?_ ?_
  · rw [map_mul]
    exact mul_le_of_le_one_of_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers R K w).mp (hk.integral 0 0 w)) (hk.lowerRight w)
  · rw [map_mul, mul_comm]
    exact mul_le_of_le_of_le_one (hk.lowerLeft w)
      ((HeightOneSpectrum.mem_adicCompletionIntegers R K w).mp (hk.integral 0 1 w))

private theorem valued_apply_zero_zero_eq_one {N : Ideal R} (hN : N ≠ ⊥)
    {k : GL (Fin 2) (FiniteAdeleRing R K)} (hk : k ∈ finiteLevelOne R K N)
    {w : HeightOneSpectrum R} (hw : w.asIdeal ∣ N) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 w) = 1 := by
  have hdet := valued_det_apply_eq_one K hk w
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hdet
  have hlt : Valued.v (((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0
      - (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det) w)
      < Valued.v ((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det w) := by
    rw [hdet, show ((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0
        - (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det) w
        = -(((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det
            - (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0) w) by
          rw [coe_sub_apply, coe_sub_apply]; ring,
      Valuation.map_neg]
    exact (valued_det_sub_apply_zero_zero_le K hk.1 w).trans_lt (idealBound_lt_one_of_dvd hN hw)
  rw [show (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0 w
      = ((k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 0 0
          - (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det) w
        + (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det w by
      rw [coe_sub_apply]; ring,
    Valuation.map_add_eq_of_lt_right _ hlt, hdet]

private theorem sub_mem_integralFiniteAdeles_adeleOn (S : Finset (HeightOneSpectrum R))
    [DecidablePred (· ∈ S)] (y y' : (w : HeightOneSpectrum R) → w.adicCompletion K)
    (a d : FiniteAdeleRing R K) (h : ∀ w ∈ S, Valued.v (a w * y w - y' w * d w) ≤ 1) :
    a * adeleOn S y - adeleOn S y' * d ∈ integralFiniteAdeles R K := by
  intro w
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_sub_apply, coe_mul_apply, coe_mul_apply]
  by_cases hw : w ∈ S
  · rw [adeleOn_apply_of_mem S y hw, adeleOn_apply_of_mem S y' hw]
    exact h w hw
  · rw [adeleOn_apply_of_not_mem S y hw, adeleOn_apply_of_not_mem S y' hw, mul_zero, zero_mul,
      sub_zero, map_zero]
    exact zero_le'

end Local

section Production

variable (F : Type) [Field F] [NumberField F]

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 w = WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 w

private theorem idealBound_mul_sq {N 𝔣 : Ideal (𝓞 F)} (hN : N ≠ ⊥) (h𝔣 : 𝔣 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (N * 𝔣 ^ 2) w
      = idealBound (𝓞 F) N w
          * WithZero.exp (-(2 * (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))) := by
  have h𝔣2 : 𝔣 * 𝔣 ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim h𝔣 h𝔣
  rw [pow_two, idealBound_mul hN h𝔣2, idealBound_mul h𝔣 h𝔣,
    idealBound_eq_exp_neg_idealMultiplicity F h𝔣, ← WithZero.exp_add]
  congr 2; ring

private theorem idealBound_mul_sq_le {N 𝔣 : Ideal (𝓞 F)} (hN : N ≠ ⊥) (h𝔣 : 𝔣 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (N * 𝔣 ^ 2) w
      ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) := by
  have h𝔣2 : 𝔣 * 𝔣 ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim h𝔣 h𝔣
  rw [← idealBound_eq_exp_neg_idealMultiplicity F h𝔣, pow_two]
  exact (idealBound_mul_le_right hN h𝔣2 w).trans (idealBound_mul_le_right h𝔣 h𝔣 w)

private theorem poleBound_adeleOn {N 𝔣 : Ideal (𝓞 F)} (hN : N ≠ ⊥) (h𝔣 : 𝔣 ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    {y : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F}
    (hy : ∀ w ∈ S, Valued.v (y w) ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))
    (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (adeleOn S y w) * idealBound (𝓞 F) (N * 𝔣 ^ 2) w ≤ idealBound (𝓞 F) N w := by
  by_cases hw : w ∈ S
  · rw [adeleOn_apply_of_mem S y hw, idealBound_mul_sq F hN h𝔣 w, mul_left_comm]
    refine mul_le_of_le_one_right' ?_
    calc Valued.v (y w) * WithZero.exp (-(2 * (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)))
        ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)
            * WithZero.exp (-(2 * (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))) :=
          mul_le_mul_left (hy w hw) _
      _ ≤ 1 := by
          rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · rw [adeleOn_apply_of_not_mem S y hw, map_zero, zero_mul]
    exact zero_le'

private theorem jointPoleBound_adeleOn {N 𝔣 : Ideal (𝓞 F)} (hN : N ≠ ⊥) (h𝔣 : 𝔣 ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)]
    {y y' : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F}
    (hy : ∀ w ∈ S, Valued.v (y w) ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))
    (hy' : ∀ w ∈ S, Valued.v (y' w) ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))
    (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (adeleOn S y' w) * Valued.v (adeleOn S y w) * idealBound (𝓞 F) (N * 𝔣 ^ 2) w
      ≤ 1 := by
  by_cases hw : w ∈ S
  · rw [adeleOn_apply_of_mem S y hw, adeleOn_apply_of_mem S y' hw, idealBound_mul_sq F hN h𝔣 w,
      mul_left_comm]
    refine (mul_le_of_le_one_right' ?_).trans (idealBound_le_one N w)
    calc Valued.v (y' w) * Valued.v (y w)
          * WithZero.exp (-(2 * (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)))
        ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)
            * WithZero.exp (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)
            * WithZero.exp (-(2 * (HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ))) :=
          mul_le_mul_left (mul_le_mul' (hy' w hw) (hy w hw)) _
      _ ≤ 1 := by
          rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          omega
  · rw [adeleOn_apply_of_not_mem S y hw, map_zero, mul_zero, zero_mul]
    exact zero_le'

end Production

end P7LevelMono

section Prints
end Prints

end
end M4aP7_LevelMonoFurniture2

section M4aP7_RamifiedTwist
noncomputable section
open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam
open AutomorphicForm.SmoothCusp

namespace P7RamTwist

open AutomorphicForm.GaussTwist
variable (F : Type) [Field F] [NumberField F]

open P7LevelMono
open scoped Classical
open FLT.SmoothVectors MeasureTheory

set_option maxSynthPendingDepth 3

private theorem mk_coe_gaussRep (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) (𝔭 : modulusPrimes F 𝔣) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
        ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
      ((gaussRep F 𝔣 u 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)
    = ((u 𝔭 : LocalGaussFactor F 𝔣 𝔭.1) : 𝔭.1.adicCompletionIntegers F
        ⧸ (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣)) :=
  P7LevelMono.mk_coe_unitQuotLift _ _ (u 𝔭)

private theorem coe_prod_apply_of_units {ι : Type*} (s : Finset ι)
    (f : ι → (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    ((∏ i ∈ s, f i : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w
      = ∏ i ∈ s, (((f i : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [coe_one_apply]
  | cons a s ha ih => simp only [Finset.prod_cons, Units.val_mul, coe_mul_apply, ih]

private theorem gaussUnitIdele_fst (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) :
    ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [gaussUnitIdele, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem gaussUnitIdele_inv_fst (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣) :
    (((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [gaussUnitIdele, ← map_inv, Units.coe_map]; exact finIncl_apply_fst (𝓞 F) F _

private theorem gaussUnitIdele_snd_apply_of_not_mem (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ modulusPrimes F 𝔣) :
    ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  classical
  rw [gaussUnitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  exact Finset.prod_eq_one fun 𝔭 _ =>
    localUnit_apply_of_ne (𝓞 F) F 𝔭.1 _ (fun h => hw (h ▸ 𝔭.2))

private theorem gaussUnitIdele_snd_apply_of_mem (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = (((gaussRep F 𝔣 u ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F) := by
  classical
  rw [gaussUnitIdele, Units.coe_map, finIncl_apply_snd, coe_prod_apply_of_units]
  refine (Finset.prod_eq_single (⟨𝔭, h𝔭⟩ : modulusPrimes F 𝔣)
    (fun 𝔮 _ h𝔮 => localUnit_apply_of_ne (𝓞 F) F 𝔮.1 _ ?_)
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · exact fun h => h𝔮 (Subtype.ext h.symm)
  · exact localUnit_apply_self (𝓞 F) F 𝔭 _

private theorem valued_gaussUnitIdele_snd_apply (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) = 1 := by
  by_cases hw : w ∈ modulusPrimes F 𝔣
  · rw [gaussUnitIdele_snd_apply_of_mem F 𝔣 u hw]
    exact P7LevelMono.valued_units_coe F w (gaussRep F 𝔣 u ⟨w, hw⟩)
  · rw [gaussUnitIdele_snd_apply_of_not_mem F 𝔣 u hw]; exact map_one _

private theorem gaussUnitIdele_inv_snd_apply_of_mem (𝔣 : Ideal (𝓞 F)) (u : GaussIndex F 𝔣)
    {𝔭 : HeightOneSpectrum (𝓞 F)} (h𝔭 : 𝔭 ∈ modulusPrimes F 𝔣) :
    (((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
      = ((((gaussRep F 𝔣 u ⟨𝔭, h𝔭⟩ : (𝔭.adicCompletionIntegers F)ˣ)
            : 𝔭.adicCompletionIntegers F) : 𝔭.adicCompletion F))⁻¹ := by
  have hprod :
      (((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
        * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭 = 1 := by
    have heq : (((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
        * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
          * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 𝔭
        = ((((gaussUnitIdele F 𝔣 u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
            * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 𝔭 := rfl
      _ = (1 : AdeleRing (𝓞 F) F).2 𝔭 := by rw [heq]
      _ = 1 := rfl
  rw [gaussUnitIdele_snd_apply_of_mem F 𝔣 u h𝔭] at hprod
  exact eq_inv_of_mul_eq_one_left hprod

private def gaussTwistFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fnTwist F η (gaussSumFn F η 𝔣 φ)

private def modulusNhd (𝔣 : Ideal (𝓞 F)) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {x | (↑x : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F
     ∧ ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F
     ∧ (↑x : AdeleRing (𝓞 F) F).2 - 1 ∈ idealBall (𝓞 F) F 𝔣}

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 v = WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 v

private theorem eta_eq_one_of_mem_modulusNhd (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ modulusNhd F 𝔣)
    (harch : (↑x : AdeleRing (𝓞 F) F).1 = 1) : η x = 1 := by
  obtain ⟨hint, hintinv, hcong⟩ := hx
  refine hmod x harch (fun v => ⟨?_, ?_⟩)
  ·
    have hle : Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) ≤ 1 := hint v
    have hinvle : Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
      hintinv v
    have hx1 : ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
        * (↑x : AdeleRing (𝓞 F) F).2 v = 1 := by
      have h : ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
          * (↑x : AdeleRing (𝓞 F) F) = 1 := x.inv_mul
      calc ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
            * (↑x : AdeleRing (𝓞 F) F).2 v
          = (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
              * (↑x : AdeleRing (𝓞 F) F)).2 v := rfl
        _ = (1 : AdeleRing (𝓞 F) F).2 v := by rw [h]
        _ = 1 := rfl
    refine le_antisymm hle ?_
    have hprod : Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
        * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, hx1, map_one]
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
            * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) := hprod.symm
      _ ≤ 1 * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) :=
          mul_le_mul_left hinvle _
      _ = Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) := one_mul _
  ·
    have hcv := hcong v
    rw [coe_sub_apply, coe_one_apply] at hcv
    exact hcv.trans_eq (idealBound_eq_exp_neg_idealMultiplicity F h𝔣 v)

private noncomputable def gaussShift (𝔣 : Ideal (𝓞 F))
    (aInt : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) : GaussIndex F 𝔣 :=
  fun 𝔭 => Units.map (Ideal.Quotient.mk _).toMonoidHom (aInt 𝔭)

private theorem coe_gaussShift (𝔣 : Ideal (𝓞 F))
    (aInt : ∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ) (𝔭 : modulusPrimes F 𝔣) :
    ((gaussShift F 𝔣 aInt 𝔭 : LocalGaussFactor F 𝔣 𝔭.1)
      : 𝔭.1.adicCompletionIntegers F
          ⧸ (IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
              ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
      = Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (𝔭.1.adicCompletionIntegers F))
            ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣))
          ((aInt 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F) :=
  Units.coe_map _ (aInt 𝔭)

set_option maxHeartbeats 1600000 in
private theorem gaussTwistFn_level_invariant (Φ : HeckeEigensystem F ℂ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U Φ.level, φ (g * u) = φ g)
    (g : AdelicGL2 (𝓞 F) F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ (productionPinsCompact F).U (Φ.level * 𝔣 ^ 2)) :
    gaussTwistFn F η 𝔣 φ (g * k) = gaussTwistFn F η 𝔣 φ g := by
  classical
  have hN := Φ.level_ne_bot
  have hN' : Φ.level * 𝔣 ^ 2 ≠ ⊥ := fun h => by
    rcases Ideal.mul_eq_bot.1 h with h | h
    · exact hN h
    · exact h𝔣 (pow_eq_zero_iff two_ne_zero |>.mp h)
  have hle : Φ.level * 𝔣 ^ 2 ≤ Φ.level := Ideal.mul_le_left
  have hklv : glFin (𝓞 F) F k ∈ finiteLevelOne (𝓞 F) F (Φ.level * 𝔣 ^ 2) :=
    glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U F (Φ.level * 𝔣 ^ 2) hk
  have hkL1 : IsLevelOneMatrix (𝓞 F) F (Φ.level * 𝔣 ^ 2)
      (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    (mem_finiteLevelOne_iff.mp hklv).1
  set kf : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)
    := (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) with hkfdef
  have hdvd : ∀ 𝔭 : modulusPrimes F 𝔣, 𝔭.1.asIdeal ∣ Φ.level * 𝔣 ^ 2 := fun 𝔭 =>
    dvd_trans ((mem_modulusPrimes F h𝔣 𝔭.1).mp 𝔭.2)
      (dvd_mul_of_dvd_right (dvd_pow_self 𝔣 two_ne_zero) Φ.level)
  have hk00 : ∀ 𝔭 : modulusPrimes F 𝔣, Valued.v ((kf 0 0) 𝔭.1) = 1 := fun 𝔭 =>
    P7LevelMono.valued_apply_zero_zero_eq_one F hN' hklv (hdvd 𝔭)
  obtain ⟨aInt, haInt⟩ :
      ∃ a : (∀ 𝔭 : modulusPrimes F 𝔣, (𝔭.1.adicCompletionIntegers F)ˣ), ∀ 𝔭,
        (((a 𝔭 : (𝔭.1.adicCompletionIntegers F)ˣ) : 𝔭.1.adicCompletionIntegers F)
          : 𝔭.1.adicCompletion F) = (kf 0 0) 𝔭.1 :=
    ⟨fun 𝔭 => P7LevelMono.unitOfValuedEqOne F 𝔭.1 _ (hk00 𝔭),
     fun 𝔭 => P7LevelMono.coe_coe_unitOfValuedEqOne F 𝔭.1 _ (hk00 𝔭)⟩
  let aClass : GaussIndex F 𝔣 := gaussShift F 𝔣 aInt
  let σ : GaussIndex F 𝔣 ≃ GaussIndex F 𝔣 := Equiv.mulLeft aClass
  have hσ : ∀ u 𝔭, (σ u) 𝔭 = aClass 𝔭 * u 𝔭 := fun u 𝔭 => rfl
  have hgaussY : ∀ u (𝔭 : modulusPrimes F 𝔣), gaussY F 𝔣 u 𝔭.1
      = (↑↑(gaussRep F 𝔣 u 𝔭) : 𝔭.1.adicCompletion F)
        * (P7LevelMono.localUnif F 𝔭.1)⁻¹
          ^ (HeckeCharacter.idealMultiplicity F 𝔭.1 𝔣) := by
    intro u 𝔭
    show (if h : 𝔭.1 ∈ modulusPrimes F 𝔣 then _ else 0) = _
    rw [dif_pos 𝔭.2]; rfl
  have hvalY : ∀ u, ∀ 𝔭 ∈ modulusPrimes F 𝔣, Valued.v (gaussY F 𝔣 u 𝔭)
      ≤ WithZero.exp (HeckeCharacter.idealMultiplicity F 𝔭 𝔣 : ℤ) := fun u 𝔭 h𝔭 => by
    rw [hgaussY u ⟨𝔭, h𝔭⟩]
    exact (P7LevelMono.valued_units_coe_mul_localUnif_inv_pow F 𝔭 _ _).le
  have hcomp : ∀ u, kf 0 0 * P7LevelMono.adeleOn (modulusPrimes F 𝔣) (gaussY F 𝔣 u)
      - P7LevelMono.adeleOn (modulusPrimes F 𝔣) (gaussY F 𝔣 (σ u)) * kf 1 1
        ∈ integralFiniteAdeles (𝓞 F) F := fun u => by
    refine P7LevelMono.sub_mem_integralFiniteAdeles_adeleOn F (modulusPrimes F 𝔣)
      (gaussY F 𝔣 u) (gaussY F 𝔣 (σ u)) (kf 0 0) (kf 1 1) (fun 𝔭 h𝔭 => ?_)
    rw [hgaussY u ⟨𝔭, h𝔭⟩, hgaussY (σ u) ⟨𝔭, h𝔭⟩]
    have hd : Valued.v ((kf 1 1) 𝔭 - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F 𝔭 𝔣 : ℤ)) := by
      have h11 := hkL1.lowerRight 𝔭
      rw [coe_sub_apply, coe_one_apply] at h11
      exact h11.trans (P7LevelMono.idealBound_mul_sq_le F hN h𝔣 𝔭)
    exact P7LevelMono.valued_compat_le_one F 𝔭 _ (aInt ⟨𝔭, h𝔭⟩) (haInt ⟨𝔭, h𝔭⟩).symm
      (gaussRep F 𝔣 u ⟨𝔭, h𝔭⟩) (gaussRep F 𝔣 (σ u) ⟨𝔭, h𝔭⟩) (by
        rw [map_mul, mk_coe_gaussRep F 𝔣 (σ u) ⟨𝔭, h𝔭⟩, mk_coe_gaussRep F 𝔣 u ⟨𝔭, h𝔭⟩,
          hσ u ⟨𝔭, h𝔭⟩, Units.val_mul]
        congr 1) hd
  have hconj : ∀ u, (gaussTrans F 𝔣 (σ u))⁻¹ * k * gaussTrans F 𝔣 u
      ∈ (productionPinsCompact F).U Φ.level := fun u =>
    P7LevelMono.finLift_unipotent_conj_mem_productionPinsCompact_U F hle hN' hk
      (P7LevelMono.poleBound_adeleOn F hN h𝔣 (modulusPrimes F 𝔣) (hvalY u))
      (P7LevelMono.poleBound_adeleOn F hN h𝔣 (modulusPrimes F 𝔣) (hvalY (σ u)))
      (P7LevelMono.jointPoleBound_adeleOn F hN h𝔣 (modulusPrimes F 𝔣) (hvalY u) (hvalY (σ u)))
      (hcomp u)
  have hphi : ∀ u, φ (g * k * gaussTrans F 𝔣 u) = φ (g * gaussTrans F 𝔣 (σ u)) := fun u => by
    have heq : g * k * gaussTrans F 𝔣 u
        = (g * gaussTrans F 𝔣 (σ u))
          * ((gaussTrans F 𝔣 (σ u))⁻¹ * k * gaussTrans F 𝔣 u) := by group
    rw [heq]; exact hinv (g * gaussTrans F 𝔣 (σ u)) _ (hconj u)
  have hkarch : glArch (𝓞 F) F k = 1 := by
    have h := hk; rw [productionPinsCompact_U] at h; exact (Subgroup.mem_inf.mp h).2
  have hdetfin : ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ)
        : AdeleRing (𝓞 F) F).2 = kf.det := by
    have h := Matrix.GeneralLinearGroup.map_det (n := Fin 2) (adeleFin (𝓞 F) F) k
    have h' := congrArg (fun z : (FiniteAdeleRing (𝓞 F) F)ˣ => (z : FiniteAdeleRing (𝓞 F) F)) h
    simp only [Units.coe_map, MonoidHom.coe_coe, adeleFin_apply] at h'
    rw [← h', Matrix.GeneralLinearGroup.val_det_apply]; rfl
  have hwt : ∀ u, ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * gaussWt F η 𝔣 u
      = gaussWt F η 𝔣 (σ u) := by
    intro u
    set z : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det k
        * gaussUnitIdele F 𝔣 u * (gaussUnitIdele F 𝔣 (σ u))⁻¹ with hzdef
    suffices hone : η z = 1 by
      unfold gaussWt
      rw [hzdef, map_mul, map_mul, map_inv] at hone
      have h := div_eq_one.mp hone
      calc ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
            * ((η (gaussUnitIdele F 𝔣 u) : ℂˣ) : ℂ)
          = ((η (Matrix.GeneralLinearGroup.det k) * η (gaussUnitIdele F 𝔣 u) : ℂˣ) : ℂ) :=
            (Units.val_mul _ _).symm
        _ = ((η (gaussUnitIdele F 𝔣 (σ u)) : ℂˣ) : ℂ) := by rw [h]
    have hz2 : ∀ w, (↑z : AdeleRing (𝓞 F) F).2 w
        = ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
          * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
          * (((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w :=
      fun w => by rw [hzdef, Units.val_mul, Units.val_mul]; rfl
    have harchz : (↑z : AdeleRing (𝓞 F) F).1 = 1 := by
      have h1 := P7LevelMono.det_fst_eq_one F hkarch
      have h2 := gaussUnitIdele_fst F 𝔣 u
      have h3 := gaussUnitIdele_inv_fst F 𝔣 (σ u)
      calc (↑z : AdeleRing (𝓞 F) F).1
          = ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
              * ((gaussUnitIdele F 𝔣 u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
              * (((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := by
            rw [hzdef, Units.val_mul, Units.val_mul]; rfl
        _ = 1 := by rw [h1, h2, h3, mul_one, mul_one]
    have hzval : ∀ w, Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w) = 1 := by
      intro w
      have hinv3 :
          Valued.v ((((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
              : AdeleRing (𝓞 F) F).2 w) = 1 := by
        have hprod :
            Valued.v ((((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
                : AdeleRing (𝓞 F) F).2 w)
              * Valued.v (((gaussUnitIdele F 𝔣 (σ u) : (AdeleRing (𝓞 F) F)ˣ)
                : AdeleRing (𝓞 F) F).2 w) = 1 := by
          rw [← map_mul,
            show (((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
                * ((gaussUnitIdele F 𝔣 (σ u) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
              = ((((gaussUnitIdele F 𝔣 (σ u))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
                  * ((gaussUnitIdele F 𝔣 (σ u) : (AdeleRing (𝓞 F) F)ˣ)
                      : AdeleRing (𝓞 F) F)).2 w from rfl,
            ← Units.val_mul, inv_mul_cancel, Units.val_one]
          exact map_one _
        rw [valued_gaussUnitIdele_snd_apply F 𝔣 (σ u) w, mul_one] at hprod
        exact hprod
      rw [hz2 w, map_mul, map_mul, P7LevelMono.valued_det_snd_eq_one F hklv w,
        valued_gaussUnitIdele_snd_apply F 𝔣 u w, hinv3, mul_one, mul_one]
    have hmem : z ∈ modulusNhd F 𝔣 := by
      refine ⟨fun w => (hzval w).le, fun w => ?_, fun w => ?_⟩
      ·
        have hzinv : Valued.v (((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w)
            * Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w) = 1 := by
          rw [← map_mul,
            show ((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
                * (↑z : AdeleRing (𝓞 F) F).2 w
              = (((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
                  * (↑z : AdeleRing (𝓞 F) F)).2 w from rfl,
            ← Units.val_mul, inv_mul_cancel, Units.val_one]
          exact map_one _
        rw [hzval w, mul_one] at hzinv
        exact hzinv.le
      ·
        rw [coe_sub_apply, coe_one_apply]
        by_cases hw : w ∈ modulusPrimes F 𝔣
        ·
          rw [hz2 w, hdetfin, gaussUnitIdele_snd_apply_of_mem F 𝔣 u hw,
            gaussUnitIdele_inv_snd_apply_of_mem F 𝔣 (σ u) hw,
            idealBound_eq_exp_neg_idealMultiplicity F h𝔣 w]
          have hdet : Valued.v (kf.det w
              - (((aInt ⟨w, hw⟩ : (w.adicCompletionIntegers F)ˣ) : w.adicCompletionIntegers F)
                  : w.adicCompletion F))
              ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) := by
            rw [haInt ⟨w, hw⟩, ← coe_sub_apply]
            exact (P7LevelMono.valued_det_sub_apply_zero_zero_le F hkL1 w).trans
              (P7LevelMono.idealBound_mul_sq_le F hN h𝔣 w)
          exact P7LevelMono.valued_det_mul_div_sub_one_le F w _ (aInt ⟨w, hw⟩) rfl
            (gaussRep F 𝔣 u ⟨w, hw⟩) (gaussRep F 𝔣 (σ u) ⟨w, hw⟩) (by
              rw [map_mul, mk_coe_gaussRep F 𝔣 (σ u) ⟨w, hw⟩, mk_coe_gaussRep F 𝔣 u ⟨w, hw⟩,
                hσ u ⟨w, hw⟩, Units.val_mul]
              congr 1) hdet
        ·
          have hwf : ¬ w.asIdeal ∣ 𝔣 := fun hd => hw ((mem_modulusPrimes F h𝔣 w).mpr hd)
          rw [idealBound_eq_one_of_not_dvd h𝔣 hwf]
          calc Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w - 1)
              ≤ max (Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w))
                  (Valued.v (1 : w.adicCompletion F)) := Valuation.map_sub _ _ _
            _ = 1 := by rw [hzval w, map_one, max_self]
    exact eta_eq_one_of_mem_modulusNhd F η h𝔣 hmod hmem harchz
  unfold gaussTwistFn gaussSumFn
  rw [fnTwist_apply, fnTwist_apply]
  unfold chiDet
  rw [map_mul, map_mul, Units.val_mul, mul_assoc]
  congr 1
  calc ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
        * ∑ u, gaussWt F η 𝔣 u * φ (g * k * gaussTrans F 𝔣 u)
      = ∑ u, (((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * gaussWt F η 𝔣 u)
          * φ (g * gaussTrans F 𝔣 (σ u)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [hphi u, ← mul_assoc]
    _ = ∑ u, gaussWt F η 𝔣 (σ u) * φ (g * gaussTrans F 𝔣 (σ u)) :=
        Finset.sum_congr rfl fun u _ => by rw [hwt u]
    _ = ∑ u', gaussWt F η 𝔣 u' * φ (g * gaussTrans F 𝔣 u') :=
        σ.sum_comp (fun u' => gaussWt F η 𝔣 u' * φ (g * gaussTrans F 𝔣 u'))

private theorem eta_det_eq_of_sTrivial (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {M : Ideal (𝓞 F)} (v : HeightOneSpectrum (𝓞 F)) (hvS : v ∉ modulusPrimes F 𝔣)
    {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsCompact F).U M) (heckeGen (𝓞 F) F v))
    (harch : glArch (𝓞 F) F x = 1)
    (hStriv : ∀ w ∈ modulusPrimes F 𝔣, finComponent (𝓞 F) F w (glFin (𝓞 F) F x) = 1) :
    η (Matrix.GeneralLinearGroup.det x)
      = η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) := by
  have _ := harch
  suffices hone : η (Matrix.GeneralLinearGroup.det x
      * (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹) = 1 by
    have h := hone
    rw [map_mul, map_inv] at h
    exact eq_of_div_eq_one h
  obtain ⟨u₁, hu₁, u₂, hu₂, hxeq⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [productionPinsCompact_U] at hu₁ hu₂
  have hu₁' := Subgroup.mem_inf.mp hu₁; have hu₂' := Subgroup.mem_inf.mp hu₂
  set z : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det x
    * (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹ with hzdef
  have hz : z = Matrix.GeneralLinearGroup.det u₁ * Matrix.GeneralLinearGroup.det u₂ := by
    rw [hzdef, ← hxeq, map_mul, map_mul, mul_right_comm,
      mul_assoc (Matrix.GeneralLinearGroup.det u₁), mul_inv_cancel, mul_one]
  have harchz : (↑z : AdeleRing (𝓞 F) F).1 = 1 := by
    rw [hz]
    have h₁ := P7LevelMono.det_fst_eq_one F hu₁'.2
    have h₂ := P7LevelMono.det_fst_eq_one F hu₂'.2
    show ((↑(Matrix.GeneralLinearGroup.det u₁) : AdeleRing (𝓞 F) F)
        * (↑(Matrix.GeneralLinearGroup.det u₂) : AdeleRing (𝓞 F) F)).1 = 1
    change (↑(Matrix.GeneralLinearGroup.det u₁) : AdeleRing (𝓞 F) F).1
        * (↑(Matrix.GeneralLinearGroup.det u₂) : AdeleRing (𝓞 F) F).1 = 1
    rw [h₁, h₂, mul_one]
  have hu₁lv : glFin (𝓞 F) F u₁ ∈ finiteLevelOne (𝓞 F) F M := (mem_levelOne_iff).mp hu₁'.1
  have hu₂lv : glFin (𝓞 F) F u₂ ∈ finiteLevelOne (𝓞 F) F M := (mem_levelOne_iff).mp hu₂'.1
  have hzval : ∀ w, Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w) = 1 := by
    intro w
    rw [hz]
    change Valued.v (((↑(Matrix.GeneralLinearGroup.det u₁) : AdeleRing (𝓞 F) F)
        * (↑(Matrix.GeneralLinearGroup.det u₂) : AdeleRing (𝓞 F) F)).2 w) = 1
    change Valued.v ((↑(Matrix.GeneralLinearGroup.det u₁) : AdeleRing (𝓞 F) F).2 w
        * (↑(Matrix.GeneralLinearGroup.det u₂) : AdeleRing (𝓞 F) F).2 w) = 1
    rw [map_mul, P7LevelMono.valued_det_snd_eq_one F hu₁lv w,
        P7LevelMono.valued_det_snd_eq_one F hu₂lv w, mul_one]
  have hzw_eq_one : ∀ w ∈ modulusPrimes F 𝔣, (↑z : AdeleRing (𝓞 F) F).2 w = 1 := by
    intro w hw
    have hwv : w ≠ v := fun he => hvS (he ▸ hw)
    have hxw : finComponent (𝓞 F) F w (glFin (𝓞 F) F x) = 1 := hStriv w hw
    have hgw : finComponent (𝓞 F) F w (glFin (𝓞 F) F (heckeGen (𝓞 F) F v)) = 1 :=
      P7LevelMono.finComponent_glFin_heckeGenAt_of_ne v _ hwv
    have hdetfin : ∀ g : AdelicGL2 (𝓞 F) F,
        (↑(Matrix.GeneralLinearGroup.det g) : AdeleRing (𝓞 F) F).2 w
          = ((Matrix.GeneralLinearGroup.det (finComponent (𝓞 F) F w (glFin (𝓞 F) F g))
              : (w.adicCompletion F)ˣ) : w.adicCompletion F) := by
      intro g
      have h1 := Matrix.GeneralLinearGroup.map_det (n := Fin 2) (adeleFin (𝓞 F) F) g
      have h2 := congrArg
        (fun y : (FiniteAdeleRing (𝓞 F) F)ˣ => (y : FiniteAdeleRing (𝓞 F) F) w) h1
      simp only [Units.coe_map, MonoidHom.coe_coe, adeleFin_apply] at h2
      have h3 := Matrix.GeneralLinearGroup.map_det (n := Fin 2)
        (finAdeleEval (𝓞 F) F w) (glFin (𝓞 F) F g)
      have h4 := congrArg (fun y : (w.adicCompletion F)ˣ => (y : w.adicCompletion F)) h3
      simp only [Units.coe_map, MonoidHom.coe_coe] at h4
      rw [← h2, show finComponent (𝓞 F) F w ((glFin (𝓞 F) F) g)
          = (Matrix.GeneralLinearGroup.map (finAdeleEval (𝓞 F) F w)) ((glFin (𝓞 F) F) g) from rfl,
        h4, finAdeleEval_apply]
      rfl
    have hginvw : (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
          : AdeleRing (𝓞 F) F).2 w = 1 := by
      have hprod : (↑(Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))
            : AdeleRing (𝓞 F) F).2 w
          * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
              : AdeleRing (𝓞 F) F).2 w = 1 := by
        have heq : (↑(Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : AdeleRing (𝓞 F) F)
            * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
                : AdeleRing (𝓞 F) F) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        calc (↑(Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : AdeleRing (𝓞 F) F).2 w
              * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
                  : AdeleRing (𝓞 F) F).2 w
            = ((↑(Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : AdeleRing (𝓞 F) F)
                * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
                    : AdeleRing (𝓞 F) F)).2 w := rfl
          _ = (1 : AdeleRing (𝓞 F) F).2 w := by rw [heq]
          _ = 1 := rfl
      rw [hdetfin (heckeGen (𝓞 F) F v), hgw, map_one, Units.val_one, one_mul] at hprod
      exact hprod
    rw [hzdef]
    change ((↑(Matrix.GeneralLinearGroup.det x) : AdeleRing (𝓞 F) F)
        * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
            : AdeleRing (𝓞 F) F)).2 w = 1
    change (↑(Matrix.GeneralLinearGroup.det x) : AdeleRing (𝓞 F) F).2 w
        * (↑((Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v))⁻¹)
            : AdeleRing (𝓞 F) F).2 w = 1
    rw [hdetfin x, hxw, map_one, Units.val_one, hginvw, one_mul]
  have hmem : z ∈ modulusNhd F 𝔣 := by
    refine ⟨fun w => (hzval w).le, fun w => ?_, fun w => ?_⟩
    ·
      have hzinv : Valued.v (((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w)
          * Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w) = 1 := by
        rw [← map_mul,
          show ((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
              * (↑z : AdeleRing (𝓞 F) F).2 w
            = (((↑z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
                * (↑z : AdeleRing (𝓞 F) F)).2 w from rfl,
          ← Units.val_mul, inv_mul_cancel, Units.val_one]
        exact map_one _
      rw [hzval w, mul_one] at hzinv
      exact hzinv.le
    ·
      rw [coe_sub_apply, coe_one_apply]
      by_cases hw : w ∈ modulusPrimes F 𝔣
      · rw [hzw_eq_one w hw, sub_self, map_zero]; exact zero_le'
      · have hwf : ¬ w.asIdeal ∣ 𝔣 := fun hd => hw ((mem_modulusPrimes F h𝔣 w).mpr hd)
        rw [idealBound_eq_one_of_not_dvd h𝔣 hwf]
        calc Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w - 1)
            ≤ max (Valued.v ((↑z : AdeleRing (𝓞 F) F).2 w))
                (Valued.v (1 : w.adicCompletion F)) := Valuation.map_sub _ _ _
          _ = 1 := by rw [hzval w, map_one, max_self]
  exact eta_eq_one_of_mem_modulusNhd F η h𝔣 hmod hmem harchz

end P7RamTwist

section Prints
end Prints

end
end M4aP7_RamifiedTwist

theorem solution
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U N, φ (g * u) = φ g)
    (g : AdelicGL2 (𝓞 F) F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ (productionPinsCompact F).U (N * 𝔣 ^ 2)) :
    fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) (g * k)
      = fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) g := by
  exact P7RamTwist.gaussTwistFn_level_invariant F ⟨N, hN, fun _ => 0, fun _ => 0⟩ η 𝔣 h𝔣 hmod hinv g k hk

end S_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant
end P2MW
export P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant (solution)
