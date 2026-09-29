-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a0931e90-78ad-5e0e-8865-7aa7c8d12033

import Mathlib
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

namespace HstdGen

variable {F : Type} [Field F] [NumberField F]

theorem eq_one_of_components (g : AdelicGL2 (𝓞 F) F) (h₁ : glArch (𝓞 F) F g = 1)
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

open HstdGen in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ N → v ∈ S)
    (hU : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ N →
      ∀ k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F),
        AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) ∈ U N) :
    ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 F) F)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 F) F), u₁ ∈ U N ∧ u₂ ∈ U N ∧
        (heckeGen (𝓞 F) F w)⁻¹ = centralScalar (𝓞 F) F z * u₁ * heckeGen (𝓞 F) F w * u₂ := by
  intro w hwS
  classical
  have hwN : ¬ w.asIdeal ∣ N := fun h => hwS (hN w h)
  let ϖ : (w.adicCompletion F)ˣ := uniformizerUnit F w
  let wI : GL (Fin 2) (w.adicCompletionIntegers F) :=
    ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  let k : GL (Fin 2) (w.adicCompletion F) :=
    Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F)) wI
  have hk : k ∈ LocalGL2.integralSubgroup (w.adicCompletionIntegers F) (w.adicCompletion F) := ⟨wI, rfl⟩
  have hkval : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j = !![(0 : w.adicCompletion F), 1; 1, 0] i j := by
    intro i j
    show algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  let u : AdelicGL2 (𝓞 F) F := AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F w k)
  have hu : u ∈ U N := hU w hwN k hk
  let z : (AdeleRing (𝓞 F) F)ˣ := Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F w ϖ⁻¹)
  refine ⟨z, u, u, hu, hu, ?_⟩
  rw [inv_eq_iff_mul_eq_one]
  have hzfst : ∀ i j : Fin 2, ((((centralScalar (𝓞 F) F z) : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by
    intro i j
    simp only [centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  have hzsnd : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ((((centralScalar (𝓞 F) F z) : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        Matrix.diagonal (fun _ => ((localUnit (𝓞 F) F w ϖ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) i j := by
    intro v i j
    simp only [centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · rfl
    · rfl
  have hArchH : glArch (𝓞 F) F (heckeGen (𝓞 F) F w) = 1 :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [glArch_apply, Units.val_one]; exact heckeGenAt_fst _ i j
  have hArchC : glArch (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 :=
    Matrix.GeneralLinearGroup.ext fun i j => by rw [glArch_apply, Units.val_one]; exact hzfst i j
  have hArchU : glArch (𝓞 F) F u = 1 := AdelicDock.glArch_finEmbed _ _ _
  have hHw : finComponent (𝓞 F) F w (glFin (𝓞 F) F (heckeGen (𝓞 F) F w)) = diagOne ϖ :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [finComponent_apply, glFin_apply, diagOne_coe_apply]; exact heckeGenAt_snd_apply_self _ i j
  have hHne : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ w →
      finComponent (𝓞 F) F v (glFin (𝓞 F) F (heckeGen (𝓞 F) F w)) = 1 := fun v hv =>
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [finComponent_apply, glFin_apply, Units.val_one]; exact heckeGenAt_snd_apply_of_ne _ hv i j
  have hUw : finComponent (𝓞 F) F w (glFin (𝓞 F) F u) = k := by
    show finComponent (𝓞 F) F w (glFin (𝓞 F) F (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F w k))) = k
    rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]
  have hUne : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ w → finComponent (𝓞 F) F v (glFin (𝓞 F) F u) = 1 := by
    intro v hv
    show finComponent (𝓞 F) F v (glFin (𝓞 F) F (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F w k))) = 1
    rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hv]
  have hCne : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ w → finComponent (𝓞 F) F v (glFin (𝓞 F) F (centralScalar (𝓞 F) F z)) = 1 :=
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

#print axioms solution

end S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem (solution)
