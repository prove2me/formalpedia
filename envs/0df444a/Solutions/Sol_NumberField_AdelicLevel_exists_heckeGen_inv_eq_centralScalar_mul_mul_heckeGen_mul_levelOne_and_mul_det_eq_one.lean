-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9d3b4f33-dc9a-501f-8795-be068764b6f3

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

namespace HstdGen

variable {F : Type} [Field F] [NumberField F]

private theorem eq_one_of_components (g : AdelicGL2 (𝓞 F) F) (h₁ : glArch (𝓞 F) F g = 1)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) : g = 1 := by
  apply Units.ext
  rw [Units.val_one]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [map_one]
    ext i j
    have e := congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing F) => (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simp only [glArch_apply, Units.val_one] at e
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact e
  · refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun v => ?_
    rw [map_one, map_one]
    ext i j : 1
    have e := congrArg (fun x : GL (Fin 2) (v.adicCompletion F) => (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) (h₂ v)
    simp only [finComponent_apply, glFin_apply, Units.val_one] at e
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact e

end HstdGen

namespace HstdL1

variable {F : Type} [Field F] [NumberField F]

private theorem finEmbed_localEmbed_mem_levelOne {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N := by
  have hN0 : N ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd hN0 hv
  obtain ⟨y, rfl⟩ := hk
  have hint : ∀ (y : GL (Fin 2) (v.adicCompletionIntegers F)) (i j : Fin 2),
      ((Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) y :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    intro y i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ((y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)) i j).2
  have hloc : ∀ (y : GL (Fin 2) (v.adicCompletionIntegers F)), AdelicDock.IsLocalLevelOne (𝓞 F) F v N
      ((Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) y :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
    intro y
    refine ⟨hint y, ?_, ?_⟩
    · rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (hint y 1 0)
    · rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (sub_mem (hint y 1 1) (one_mem _))
  rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff, AdelicDock.mem_localLevelOne_iff,
    ← map_inv]
  exact ⟨hloc y, hloc y⁻¹⟩

private theorem finEmbed_mem_finiteAdelicGL2Subgroup (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    AdelicDock.finEmbed (𝓞 F) F g ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed _ _ _)

end HstdL1

open HstdGen HstdL1 in

theorem solution
    (L : Type) [Field L] [NumberField L]
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ N → v ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L),
        u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ ∧
        z * Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w) = 1 := by
  intro w hwS
  classical
  have hwN : ¬ w.asIdeal ∣ N := fun h => hwS (hN w h)
  let ϖ : (w.adicCompletion L)ˣ := uniformizerUnit L w
  let wI : GL (Fin 2) (w.adicCompletionIntegers L) :=
    ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let k : GL (Fin 2) (w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) wI
  have hk : k ∈ LocalGL2.integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) := ⟨wI, rfl⟩
  have hkval : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j = !![(0 : w.adicCompletion L), 1; 1, 0] i j := by
    intro i j
    show algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers L)) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  let u : AdelicGL2 (𝓞 L) L := AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w k)
  have hu : u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
    ⟨finEmbed_localEmbed_mem_levelOne hwN hk, finEmbed_mem_finiteAdelicGL2Subgroup _⟩
  let z : (AdeleRing (𝓞 L) L)ˣ := Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w ϖ⁻¹)
  refine ⟨z, u, u, hu, hu, ?_, ?_⟩
  swap
  ·
    have hdet : Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w) =
        Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w ϖ) := by
      apply Units.ext
      show Matrix.det ((heckeGen (𝓞 L) L w : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = _
      rw [show ((heckeGen (𝓞 L) L w : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
        Matrix.diagonal ![((Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w ϖ) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]
        from rfl, Matrix.det_diagonal]
      simp
    rw [hdet, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  rw [inv_eq_iff_mul_eq_one]
  have hzfst : ∀ i j : Fin 2, ((((centralScalar (𝓞 L) L z) : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
    intro i j
    simp only [centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  have hzsnd : ∀ (v : HeightOneSpectrum (𝓞 L)) (i j : Fin 2),
      ((((centralScalar (𝓞 L) L z) : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 v =
        Matrix.diagonal (fun _ => ((localUnit (𝓞 L) L w ϖ⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) i j := by
    intro v i j
    simp only [centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · rfl
    · rfl
  have hArchH : glArch (𝓞 L) L (heckeGen (𝓞 L) L w) = 1 :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [glArch_apply, Units.val_one]; exact heckeGenAt_fst _ i j
  have hArchC : glArch (𝓞 L) L (centralScalar (𝓞 L) L z) = 1 :=
    Matrix.GeneralLinearGroup.ext fun i j => by rw [glArch_apply, Units.val_one]; exact hzfst i j
  have hArchU : glArch (𝓞 L) L u = 1 := AdelicDock.glArch_finEmbed _ _ _
  have hHw : finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w)) = diagOne ϖ :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [finComponent_apply, glFin_apply, diagOne_coe_apply]; exact heckeGenAt_snd_apply_self _ i j
  have hHne : ∀ v : HeightOneSpectrum (𝓞 L), v ≠ w →
      finComponent (𝓞 L) L v (glFin (𝓞 L) L (heckeGen (𝓞 L) L w)) = 1 := fun v hv =>
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [finComponent_apply, glFin_apply, Units.val_one]; exact heckeGenAt_snd_apply_of_ne _ hv i j
  have hUw : finComponent (𝓞 L) L w (glFin (𝓞 L) L u) = k := by
    show finComponent (𝓞 L) L w (glFin (𝓞 L) L (AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w k))) = k
    rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]
  have hUne : ∀ v : HeightOneSpectrum (𝓞 L), v ≠ w → finComponent (𝓞 L) L v (glFin (𝓞 L) L u) = 1 := by
    intro v hv
    show finComponent (𝓞 L) L v (glFin (𝓞 L) L (AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w k))) = 1
    rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hv]
  have hCne : ∀ v : HeightOneSpectrum (𝓞 L), v ≠ w → finComponent (𝓞 L) L v (glFin (𝓞 L) L (centralScalar (𝓞 L) L z)) = 1 :=
    fun v hv => Matrix.GeneralLinearGroup.ext fun i j => by
      rw [finComponent_apply, glFin_apply, hzsnd, localUnit_apply_of_ne _ _ _ _ hv, Units.val_one, Matrix.diagonal_apply, Matrix.one_apply]
  apply eq_one_of_components
  · rw [map_mul, map_mul, map_mul, map_mul, hArchH, hArchC, hArchU]; simp
  · intro v
    by_cases hv : v = w
    · subst hv
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hHw, hUw]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, hkval,
        finComponent_apply, glFin_apply, hzsnd, localUnit_apply_self]
      fin_cases i <;> fin_cases j <;> simp
    · rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hHne v hv, hUne v hv, hCne v hv]
      simp

end S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne_and_mul_det_eq_one (solution)
