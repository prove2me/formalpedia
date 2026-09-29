-- Prove2me | solution 1 for LanglandsTunnell.isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/477fb1f4-4280-55c4-ae27-db455e027f62

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
import Theorems.Thm_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option Elab.async false

open NumberField AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain NumberField.AdelicLevel

section M4aP7_LevelMono
noncomputable section
open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam
open AutomorphicForm.SmoothCusp

namespace P7LevelMono

section Rebase

variable {G : Type*} [Group G]

private theorem doubleCoset_mono {U U' : Subgroup G} (hle : U' ≤ U) (g : G) :
    HeckePair.doubleCoset U' g ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨a, hle ha, b, hle hb, rfl⟩

private theorem quotient_eq_of_quotient_eq {U U' : Subgroup G} (hle : U' ≤ U) {g : G}
    (hkey : ∀ x ∈ U', g⁻¹ * x * g ∈ U → g⁻¹ * x * g ∈ U')
    {x y : G} (hx : x ∈ HeckePair.doubleCoset U' g) (hy : y ∈ HeckePair.doubleCoset U' g)
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk y) :
    (QuotientGroup.mk x : G ⧸ U') = QuotientGroup.mk y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  rw [QuotientGroup.eq] at h ⊢
  have hw : g⁻¹ * (a⁻¹ * c) * g ∈ U := by
    have : g⁻¹ * (a⁻¹ * c) * g = b * ((a * g * b)⁻¹ * (c * g * d)) * d⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (hle hb) h) (inv_mem (hle hd))
  have hw' : g⁻¹ * (a⁻¹ * c) * g ∈ U' := hkey _ (mul_mem (inv_mem ha) hc) hw
  have : (a * g * b)⁻¹ * (c * g * d) = b⁻¹ * (g⁻¹ * (a⁻¹ * c) * g) * d := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hb) hw') hd

private theorem sum_eq_sum_of_le {U U' : Subgroup G} (hle : U' ≤ U) {g : G} {n : ℕ}
    {reps reps' : Fin n → G} (hsys : IsHeckeCosetSystem U g reps)
    (hsys' : IsHeckeCosetSystem U' g reps')
    (hkey : ∀ x ∈ U', g⁻¹ * x * g ∈ U → g⁻¹ * x * g ∈ U')
    {M : Type*} [AddCommMonoid M] (φ : G → M) (hinv : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x)
    (x : G) :
    ∑ i, φ (x * reps' i) = ∑ i, φ (x * reps i) := by
  classical
  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps' i) : G ⧸ U) = QuotientGroup.mk (reps j) :=
    fun i => hsys.covers _ (doubleCoset_mono hle g (hsys'.mem_doubleCoset i))
  choose σ hσ using hcov
  have hσinj : Function.Injective σ := by
    intro i i' hii'
    have h1 : (QuotientGroup.mk (reps' i) : G ⧸ U) = QuotientGroup.mk (reps' i') := by
      rw [hσ i, hσ i', hii']
    exact hsys'.mk_injective
      (quotient_eq_of_quotient_eq hle hkey (hsys'.mem_doubleCoset i) (hsys'.mem_doubleCoset i') h1)
  have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  have hterm : ∀ i, φ (x * reps' i) = φ (x * reps (σ i)) := by
    intro i
    have hmem : (reps (σ i))⁻¹ * reps' i ∈ U := QuotientGroup.eq.mp (hσ i).symm
    have : x * reps' i = x * reps (σ i) * ((reps (σ i))⁻¹ * reps' i) := by group
    rw [this, hinv _ _ hmem]
  calc ∑ i, φ (x * reps' i) = ∑ i, φ (x * reps (σ i)) := Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ j, φ (x * reps j) := hσbij.sum_comp (fun j => φ (x * reps j))

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

private theorem isLevelOneMatrix_mono {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (hm : IsLevelOneMatrix R K N' m) :
    IsLevelOneMatrix R K N m where
  integral := hm.integral
  lowerLeft := idealBall_mono hle hN' hm.lowerLeft
  lowerRight := idealBall_mono hle hN' hm.lowerRight

private theorem finiteLevelOne_mono {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥) :
    finiteLevelOne R K N' ≤ finiteLevelOne R K N := fun _ hg =>
  ⟨isLevelOneMatrix_mono hle hN' hg.1, isLevelOneMatrix_mono hle hN' hg.2⟩

private theorem levelOne_mono {N N' : Ideal R} (hle : N' ≤ N) (hN' : N' ≠ ⊥) :
    levelOne R K N' ≤ levelOne R K N := Subgroup.comap_mono (finiteLevelOne_mono hle hN')

end Antitone

section Key

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem finComponent_glFin_heckeGenAt_of_ne (v : HeightOneSpectrum R) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    finComponent R K w (glFin R K (heckeGenAt R K v t)) = 1 := by
  ext i j
  rw [finComponent_apply, glFin_apply, heckeGenAt_snd_apply_of_ne t hw, Units.val_one]

private theorem isLevelOneMatrix_of_offPlace {N' : Ideal R} (hN' : N' ≠ ⊥) (v : HeightOneSpectrum R)
    (hv : ¬ v.asIdeal ∣ N') {m x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (hx : IsLevelOneMatrix R K N' x) (hint : ∀ i j, m i j ∈ integralFiniteAdeles R K)
    (hoff : ∀ w : HeightOneSpectrum R, w ≠ v → ∀ i j, m i j w = x i j w) :
    IsLevelOneMatrix R K N' m where
  integral := hint
  lowerLeft := by
    intro w
    by_cases hw : w = v
    · rw [hw, idealBound_eq_one_of_not_dvd hN' hv]
      exact valued_apply_le_one (hint 1 0) v
    · rw [hoff w hw]
      exact hx.lowerLeft w
  lowerRight := by
    intro w
    by_cases hw : w = v
    · rw [hw, idealBound_eq_one_of_not_dvd hN' hv, coe_sub_apply, coe_one_apply]
      calc Valued.v (m 1 1 v - 1)
          ≤ max (Valued.v (m 1 1 v)) (Valued.v (1 : v.adicCompletion K)) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (valued_apply_le_one (hint 1 1) v) (by rw [map_one])
    · have : (m 1 1 - 1) w = (x 1 1 - 1) w := by rw [coe_sub_apply, coe_sub_apply, hoff w hw]
      rw [this]
      exact hx.lowerRight w

private theorem key_finiteLevelOne {N N' : Ideal R} (hN' : N' ≠ ⊥) (v : HeightOneSpectrum R)
    (hv : ¬ v.asIdeal ∣ N') (t : (v.adicCompletion K)ˣ)
    {x : GL (Fin 2) (FiniteAdeleRing R K)} (hx : x ∈ finiteLevelOne R K N')
    (hy : (glFin R K (heckeGenAt R K v t))⁻¹ * x * glFin R K (heckeGenAt R K v t)
      ∈ finiteLevelOne R K N) :
    (glFin R K (heckeGenAt R K v t))⁻¹ * x * glFin R K (heckeGenAt R K v t)
      ∈ finiteLevelOne R K N' := by
  have hGw : ∀ w : HeightOneSpectrum R, w ≠ v →
      finComponent R K w (glFin R K (heckeGenAt R K v t)) = 1 :=
    fun w hw => finComponent_glFin_heckeGenAt_of_ne v t hw
  have hoff : ∀ y z : GL (Fin 2) (FiniteAdeleRing R K),
      (∀ w : HeightOneSpectrum R, w ≠ v → finComponent R K w y = finComponent R K w z) →
      ∀ w : HeightOneSpectrum R, w ≠ v → ∀ i j,
        (y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w
          = (z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w := by
    intro y z h w hw i j
    show (finComponent R K w y : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
      = (finComponent R K w z : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
    rw [h w hw]
  have hconj : ∀ w : HeightOneSpectrum R, w ≠ v →
      finComponent R K w ((glFin R K (heckeGenAt R K v t))⁻¹ * x * glFin R K (heckeGenAt R K v t))
        = finComponent R K w x := by
    intro w hw
    rw [map_mul, map_mul, map_inv, hGw w hw, inv_one, one_mul, mul_one]
  have hconj' : ∀ w : HeightOneSpectrum R, w ≠ v →
      finComponent R K w
          ((glFin R K (heckeGenAt R K v t))⁻¹ * x * glFin R K (heckeGenAt R K v t))⁻¹
        = finComponent R K w x⁻¹ := by
    intro w hw
    rw [map_inv, hconj w hw, map_inv]
  exact ⟨isLevelOneMatrix_of_offPlace hN' v hv hx.1 hy.1.integral (hoff _ _ hconj),
    isLevelOneMatrix_of_offPlace hN' v hv hx.2 hy.2.integral (hoff _ _ hconj')⟩

end Key

section Transport

variable (F : Type) [Field F] [NumberField F]

private theorem productionPinsCompact_U_mono {N N' : Ideal (𝓞 F)} (hle : N' ≤ N) (hN' : N' ≠ ⊥) :
    (productionPinsCompact F).U N' ≤ (productionPinsCompact F).U N := by
  simp only [productionPinsCompact_U]
  exact inf_le_inf_right _ (levelOne_mono hle hN')

private theorem key_productionPinsCompact_U {N N' : Ideal (𝓞 F)} (hN' : N' ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N')
    (x : AdelicGL2 (𝓞 F) F) (hx : x ∈ (productionPinsCompact F).U N')
    (hy : (heckeGen (𝓞 F) F v)⁻¹ * x * heckeGen (𝓞 F) F v ∈ (productionPinsCompact F).U N) :
    (heckeGen (𝓞 F) F v)⁻¹ * x * heckeGen (𝓞 F) F v ∈ (productionPinsCompact F).U N' := by
  rw [productionPinsCompact_U] at hx hy ⊢
  refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hy).2⟩
  have hx1 := (Subgroup.mem_inf.mp hx).1
  have hy1 := (Subgroup.mem_inf.mp hy).1
  rw [mem_levelOne_iff] at hx1 hy1 ⊢
  rw [map_mul, map_mul, map_inv] at hy1 ⊢
  exact key_finiteLevelOne hN' v hv (uniformizerUnit F v) hx1 hy1

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

private theorem glArch_heckeGenAt (v : HeightOneSpectrum R) (t : (v.adicCompletion K)ˣ) :
    glArch R K (heckeGenAt R K v t) = 1 := by
  ext i j
  rw [glArch_apply, heckeGenAt_fst, Units.val_one]

private theorem glArch_eq_one_of_mem_doubleCoset {U : Subgroup (GL (Fin 2) (AdeleRing R K))}
    (hU : U ≤ (glArch R K).ker) {g : GL (Fin 2) (AdeleRing R K)} (hg : glArch R K g = 1)
    {x : GL (Fin 2) (AdeleRing R K)} (hx : x ∈ HeckePair.doubleCoset U g) :
    glArch R K x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hU ha), MonoidHom.mem_ker.mp (hU hb), hg,
    one_mul, one_mul]

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

private theorem adeleOn_apply_of_not_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) {w : HeightOneSpectrum R}
    (hw : w ∉ S) : adeleOn S y w = 0 := by
  rw [adeleOn_apply, if_neg hw]

private def maskPair (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j =>
    (⟨fun w => if P w then m i j w
        else (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w,
      (m i j).2.mono fun w hw => by
        dsimp only at hw ⊢
        split_ifs
        · exact hw
        · exact (IsLevelOneMatrix.one (R := R) (K := K) (N := ⊤)).integral i j w⟩ :
      FiniteAdeleRing R K)

private theorem maskPair_apply (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) (i j : Fin 2) (w : HeightOneSpectrum R) :
    maskPair P m i j w
      = if P w then m i j w else (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w :=
  rfl

private theorem mapMatrix_maskPair_of_pos (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) {w : HeightOneSpectrum R} (hw : P w) :
    (finAdeleEval R K w).mapMatrix (maskPair P m) = (finAdeleEval R K w).mapMatrix m := by
  ext i j
  show maskPair P m i j w = m i j w
  rw [maskPair_apply, if_pos hw]

private theorem mapMatrix_maskPair_of_neg (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) {w : HeightOneSpectrum R} (hw : ¬ P w) :
    (finAdeleEval R K w).mapMatrix (maskPair P m) = (finAdeleEval R K w).mapMatrix 1 := by
  ext i j
  show maskPair P m i j w = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w
  rw [maskPair_apply, if_neg hw]

private theorem matrix_eq_of_components {M M' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (finAdeleEval R K w).mapMatrix M = (finAdeleEval R K w).mapMatrix M') : M = M' := by
  ext i j w
  exact congrFun (congrFun (h w) i) j

private theorem maskPair_one (P : HeightOneSpectrum R → Prop) [DecidablePred P] :
    maskPair (R := R) (K := K) P 1 = 1 :=
  matrix_eq_of_components fun w => by
    by_cases hw : P w
    · rw [mapMatrix_maskPair_of_pos P _ hw]
    · rw [mapMatrix_maskPair_of_neg P _ hw]

private theorem maskPair_mul (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    maskPair P m * maskPair P m' = maskPair P (m * m') :=
  matrix_eq_of_components fun w => by
    by_cases hw : P w
    · rw [map_mul, mapMatrix_maskPair_of_pos P _ hw, mapMatrix_maskPair_of_pos P _ hw,
        mapMatrix_maskPair_of_pos P _ hw, map_mul]
    · rw [map_mul, mapMatrix_maskPair_of_neg P _ hw, mapMatrix_maskPair_of_neg P _ hw,
        mapMatrix_maskPair_of_neg P _ hw, map_one, mul_one]

private theorem isLevelOneMatrix_maskPair (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    {N : Ideal R} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (hm : IsLevelOneMatrix R K N m) : IsLevelOneMatrix R K N (maskPair P m) where
  integral := by
    intro i j w
    rw [maskPair_apply]
    split_ifs
    · exact hm.integral i j w
    · exact (IsLevelOneMatrix.one (R := R) (K := K) (N := N)).integral i j w
  lowerLeft := by
    intro w
    rw [maskPair_apply]
    split_ifs
    · exact hm.lowerLeft w
    · exact (IsLevelOneMatrix.one (R := R) (K := K) (N := N)).lowerLeft w
  lowerRight := by
    intro w
    rw [coe_sub_apply, maskPair_apply]
    split_ifs
    · exact hm.lowerRight w
    · exact (IsLevelOneMatrix.one (R := R) (K := K) (N := N)).lowerRight w

private def maskLift (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (g : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (FiniteAdeleRing R K) where
  val := maskPair P (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  inv := maskPair P
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  val_inv := by rw [maskPair_mul, Units.mul_inv, maskPair_one]
  inv_val := by rw [maskPair_mul, Units.inv_mul, maskPair_one]

private theorem maskLift_mul (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (g h : GL (Fin 2) (FiniteAdeleRing R K)) :
    maskLift P (g * h) = maskLift P g * maskLift P h := by
  apply Units.ext
  show maskPair P ((g * h : GL (Fin 2) (FiniteAdeleRing R K))
      : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
    = maskPair P (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
        * maskPair P (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  rw [maskPair_mul, Units.val_mul]

private theorem finComponent_maskLift_of_pos (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    (g : GL (Fin 2) (FiniteAdeleRing R K)) {w : HeightOneSpectrum R} (hw : P w) :
    finComponent R K w (maskLift P g) = finComponent R K w g := by
  ext i j
  rw [finComponent_apply, finComponent_apply]
  show maskPair P (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w = _
  rw [maskPair_apply, if_pos hw]

private theorem maskLift_eq_one (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    {g : GL (Fin 2) (FiniteAdeleRing R K)} (hg : ∀ w, P w → finComponent R K w g = 1) :
    maskLift P g = 1 := by
  refine Units.ext (matrix_eq_of_components fun w => ?_)
  by_cases hw : P w
  · show (finAdeleEval R K w).mapMatrix
        (maskPair P (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) = _
    rw [mapMatrix_maskPair_of_pos P _ hw, Units.val_one, map_one]
    exact congrArg
      (fun u : GL (Fin 2) (w.adicCompletion K) => (u : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)))
      (hg w hw)
  · show (finAdeleEval R K w).mapMatrix
        (maskPair P (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))) = _
    rw [mapMatrix_maskPair_of_neg P _ hw, Units.val_one]

private theorem maskLift_mem_finiteLevelOne (P : HeightOneSpectrum R → Prop) [DecidablePred P]
    {N : Ideal R} {g : GL (Fin 2) (FiniteAdeleRing R K)} (hg : g ∈ finiteLevelOne R K N) :
    maskLift P g ∈ finiteLevelOne R K N :=
  ⟨isLevelOneMatrix_maskPair P hg.1, isLevelOneMatrix_maskPair P hg.2⟩

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

private theorem isHeckeCosetSystem_mul_right {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι : Type*} {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) (k : ι → G)
    (hk : ∀ i, k i ∈ U) :
    IsHeckeCosetSystem U g (fun i => reps i * k i) where
  mem_doubleCoset i := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨a, ha, b * k i, mul_mem hb (hk i),
      by rw [← hab]; group⟩
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨i, hi.trans (QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk i))⟩
  mk_injective i j hij := by
    have hij' : (QuotientGroup.mk (reps i * k i) : G ⧸ U) = QuotientGroup.mk (reps j * k j) := hij
    have hi : (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps i * k i) :=
      QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk i)
    have hj : (QuotientGroup.mk (reps j) : G ⧸ U) = QuotientGroup.mk (reps j * k j) :=
      QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk j)
    exact hsys.mk_injective (hi.trans (hij'.trans hj.symm))

private def eraseCorr (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (x : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (AdeleRing R K) :=
  (finLift (maskLift (· ∈ S) (glFin R K x)))⁻¹

private def eraseAt (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (x : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (AdeleRing R K) :=
  x * eraseCorr S x

private theorem glArch_eraseAt (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (x : GL (Fin 2) (AdeleRing R K)) : glArch R K (eraseAt S x) = glArch R K x := by
  unfold eraseAt eraseCorr
  rw [map_mul, map_inv, glArch_finLift, inv_one, mul_one]

private theorem glFin_eraseAt (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (x : GL (Fin 2) (AdeleRing R K)) :
    glFin R K (eraseAt S x) = glFin R K x * (maskLift (· ∈ S) (glFin R K x))⁻¹ := by
  unfold eraseAt eraseCorr
  rw [map_mul, map_inv, glFin_finLift]

private theorem finComponent_eraseAt_of_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (x : GL (Fin 2) (AdeleRing R K)) {w : HeightOneSpectrum R} (hw : w ∈ S) :
    finComponent R K w (glFin R K (eraseAt S x)) = 1 := by
  rw [glFin_eraseAt, map_mul, map_inv, finComponent_maskLift_of_pos _ _ hw, mul_inv_cancel]

private theorem maskLift_glFin_heckeGenAt (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    {v : HeightOneSpectrum R} (hv : v ∉ S) (t : (v.adicCompletion K)ˣ) :
    maskLift (· ∈ S) (glFin R K (heckeGenAt R K v t)) = 1 :=
  maskLift_eq_one _ fun _ hw =>
    finComponent_glFin_heckeGenAt_of_ne v t (ne_of_mem_of_not_mem hw hv)

private theorem eraseCorr_mem (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    {N : Ideal R} {v : HeightOneSpectrum R} (hv : v ∉ S) (t : (v.adicCompletion K)ˣ)
    {x : GL (Fin 2) (AdeleRing R K)}
    (hx : x ∈ HeckePair.doubleCoset (levelOne R K N ⊓ (glArch R K).ker) (heckeGenAt R K v t)) :
    eraseCorr S x ∈ levelOne R K N ⊓ (glArch R K).ker := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  unfold eraseCorr
  refine inv_mem (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [mem_levelOne_iff, glFin_finLift, map_mul, map_mul, maskLift_mul, maskLift_mul,
      maskLift_glFin_heckeGenAt S hv t, mul_one]
    exact mul_mem (maskLift_mem_finiteLevelOne _ (Subgroup.mem_inf.mp ha).1)
      (maskLift_mem_finiteLevelOne _ (Subgroup.mem_inf.mp hb).1)
  · rw [MonoidHom.mem_ker, glArch_finLift]

private theorem isHeckeCosetSystem_eraseAt (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    {N : Ideal R} {v : HeightOneSpectrum R} (hv : v ∉ S) (t : (v.adicCompletion K)ˣ)
    {ι : Type*} {reps : ι → GL (Fin 2) (AdeleRing R K)}
    (hsys : IsHeckeCosetSystem (levelOne R K N ⊓ (glArch R K).ker) (heckeGenAt R K v t) reps) :
    IsHeckeCosetSystem (levelOne R K N ⊓ (glArch R K).ker) (heckeGenAt R K v t)
      (fun i => eraseAt S (reps i)) :=
  isHeckeCosetSystem_mul_right hsys (fun i => eraseCorr S (reps i)) fun i =>
    eraseCorr_mem S hv t (hsys.mem_doubleCoset i)

private theorem gl_ext {x y : GL (Fin 2) (AdeleRing R K)} (ha : glArch R K x = glArch R K y)
    (hf : ∀ w : HeightOneSpectrum R,
      finComponent R K w (glFin R K x) = finComponent R K w (glFin R K y)) : x = y := by
  apply Units.ext
  refine matrix_eq_of_parts ?_ (matrix_eq_of_components fun w => ?_)
  · exact congrArg
      (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))
      ha
  · exact congrArg
      (fun u : GL (Fin 2) (w.adicCompletion K) => (u : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)))
      (hf w)

end FinSurgery

section FinSurgeryProduction

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in
private theorem exists_isHeckeCosetSystem_sTrivial (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (h : ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem ((productionPinsCompact F).U N) (heckeGen (𝓞 F) F v) reps) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem ((productionPinsCompact F).U N) (heckeGen (𝓞 F) F v) reps ∧
      (∀ i, glArch (𝓞 F) F (reps i) = 1) ∧
      (∀ i, ∀ w ∈ S, finComponent (𝓞 F) F w (glFin (𝓞 F) F (reps i)) = 1) := by
  obtain ⟨reps, hsys⟩ := h
  rw [productionPinsCompact_U] at hsys ⊢
  refine ⟨fun i => eraseAt S (reps i), isHeckeCosetSystem_eraseAt S hv _ hsys, fun i => ?_,
    fun i w hw => finComponent_eraseAt_of_mem S (reps i) hw⟩
  rw [glArch_eraseAt]
  exact glArch_eq_one_of_mem_doubleCoset inf_le_right (glArch_heckeGenAt v _)
    (hsys.mem_doubleCoset i)

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

private theorem finComponent_unipotentGL2 (w : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
    finComponent R K w (unipotentGL2 a) = unipotentGL2 (a w) := by
  ext i j
  rw [finComponent_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem finComponent_unipotentGL2_adeleOn_of_not_mem (S : Finset (HeightOneSpectrum R))
    [DecidablePred (· ∈ S)] (y : (w : HeightOneSpectrum R) → w.adicCompletion K)
    {w : HeightOneSpectrum R} (hw : w ∉ S) :
    finComponent R K w (unipotentGL2 (adeleOn S y)) = 1 := by
  rw [finComponent_unipotentGL2, adeleOn_apply_of_not_mem S y hw, unipotentGL2_zero]

private theorem commute_finLift_unipotentGL2_adeleOn (S : Finset (HeightOneSpectrum R))
    [DecidablePred (· ∈ S)] (y : (w : HeightOneSpectrum R) → w.adicCompletion K)
    {x : GL (Fin 2) (AdeleRing R K)} (hx : ∀ w ∈ S, finComponent R K w (glFin R K x) = 1) :
    x * finLift (unipotentGL2 (adeleOn S y)) = finLift (unipotentGL2 (adeleOn S y)) * x := by
  refine gl_ext ?_ fun w => ?_
  · rw [map_mul, map_mul, glArch_finLift, mul_one, one_mul]
  · rw [map_mul, map_mul, map_mul, map_mul, glFin_finLift]
    by_cases hw : w ∈ S
    · rw [hx w hw, one_mul, mul_one]
    · rw [finComponent_unipotentGL2_adeleOn_of_not_mem S y hw, one_mul, mul_one]

end Generic

section Production

variable (F : Type) [Field F] [NumberField F]

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

end Local

section Production

variable (F : Type) [Field F] [NumberField F]

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 w = WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 w

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

private theorem isHeckeCosetEigenfunctionAt_gaussTwistFn (Φ : HeckeEigensystem F ℂ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {av : ℂ} (v : HeightOneSpectrum (𝓞 F))
    (hvS : v ∉ modulusPrimes F 𝔣) (hvdvd : ¬ v.asIdeal ∣ Φ.level * 𝔣 ^ 2)
    (hsys' : ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem ((productionPinsCompact F).U (Φ.level * 𝔣 ^ 2)) (heckeGen (𝓞 F) F v) reps)
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U Φ.level, φ (g * u) = φ g)
    (_hinv' : ∀ g, ∀ k ∈ (productionPinsCompact F).U (Φ.level * 𝔣 ^ 2),
      gaussTwistFn F η 𝔣 φ (g * k) = gaussTwistFn F η 𝔣 φ g)
    (heig : IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U Φ.level)
      (heckeGen (𝓞 F) F v) v φ av) :
    IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U (Φ.level * 𝔣 ^ 2))
      (heckeGen (𝓞 F) F v) v (gaussTwistFn F η 𝔣 φ)
      (((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * av) := by
  classical
  have hN' : Φ.level * 𝔣 ^ 2 ≠ ⊥ := fun h => by
    rcases Ideal.mul_eq_bot.1 h with h | h
    · exact Φ.level_ne_bot h
    · exact h𝔣 (pow_eq_zero_iff two_ne_zero |>.mp h)
  obtain ⟨reps', hsys'', harch', hStriv⟩ :=
    P7LevelMono.exists_isHeckeCosetSystem_sTrivial F (Φ.level * 𝔣 ^ 2) (modulusPrimes F 𝔣) v hvS hsys'
  refine ⟨reps', hsys'', fun g => ?_⟩
  unfold heckeCosetSum gaussTwistFn gaussSumFn
  obtain ⟨reps, hsys, hsum⟩ := heig
  have hle : (productionPinsCompact F).U (Φ.level * 𝔣 ^ 2) ≤ (productionPinsCompact F).U Φ.level :=
    P7LevelMono.productionPinsCompact_U_mono F Ideal.mul_le_left hN'
  have hrebase : ∀ x : AdelicGL2 (𝓞 F) F,
      ∑ i, φ (x * reps' i) = av * φ x := by
    intro x
    have h := P7LevelMono.sum_eq_sum_of_le (U := (productionPinsCompact F).U Φ.level)
      (U' := (productionPinsCompact F).U (Φ.level * 𝔣 ^ 2)) hle hsys hsys''
      (fun y hy hz => P7LevelMono.key_productionPinsCompact_U F hN' v hvdvd y hy hz)
      φ (fun y u hu => hinv y u hu) x
    rw [h]; exact hsum x
  have hcomm : ∀ i u, reps' i * gaussTrans F 𝔣 u = gaussTrans F 𝔣 u * reps' i := fun i u => by
    unfold gaussTrans
    exact P7LevelMono.commute_finLift_unipotentGL2_adeleOn (modulusPrimes F 𝔣) (gaussY F 𝔣 u)
      (fun w hw => hStriv i w hw)
  have hetadet : ∀ i, η (Matrix.GeneralLinearGroup.det (reps' i))
      = η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) := fun i =>
    eta_det_eq_of_sTrivial F η 𝔣 h𝔣 hmod v hvS (hsys''.mem_doubleCoset i) (harch' i)
      (fun w hw => hStriv i w hw)
  calc ∑ i, fnTwist F η (fun g' => ∑ u, gaussWt F η 𝔣 u * φ (g' * gaussTrans F 𝔣 u))
          (g * reps' i)
      = ∑ i, chiDet (𝓞 F) F η (g * reps' i)
          * ∑ u, gaussWt F η 𝔣 u * φ (g * reps' i * gaussTrans F 𝔣 u) := by
        refine Finset.sum_congr rfl fun i _ => ?_; rfl
    _ = ∑ i, (chiDet (𝓞 F) F η g
            * ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ))
          * ∑ u, gaussWt F η 𝔣 u * φ ((g * gaussTrans F 𝔣 u) * reps' i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        · unfold chiDet
          rw [map_mul, map_mul, Units.val_mul, hetadet i]
        · exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc, hcomm i u, ← mul_assoc]
    _ = (chiDet (𝓞 F) F η g
            * ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ))
          * ∑ u, gaussWt F η 𝔣 u * ∑ i, φ ((g * gaussTrans F 𝔣 u) * reps' i) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
    _ = (chiDet (𝓞 F) F η g
            * ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ))
          * ∑ u, gaussWt F η 𝔣 u * (av * φ (g * gaussTrans F 𝔣 u)) := by
        congr 1
        exact Finset.sum_congr rfl fun u _ => by rw [hrebase (g * gaussTrans F 𝔣 u)]
    _ = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * av
          * fnTwist F η (fun g' => ∑ u, gaussWt F η 𝔣 u * φ (g' * gaussTrans F 𝔣 u)) g := by
        simp only [fnTwist_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring

end P7RamTwist

section Prints
end Prints

end
end M4aP7_RamifiedTwist

theorem solution
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F))
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {av : ℂ} (v : HeightOneSpectrum (𝓞 F))
    (hvdvd : ¬ v.asIdeal ∣ N * 𝔣 ^ 2)
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U N, φ (g * u) = φ g)
    (heig : IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U N)
      (heckeGen (𝓞 F) F v) v φ av) :
    IsHeckeCosetEigenfunctionAt F ((productionPinsCompact F).U (N * 𝔣 ^ 2))
      (heckeGen (𝓞 F) F v) v (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ))
      (((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * av) := by
  have hN : N ≠ ⊥ := fun h => hvdvd (Dvd.intro ⊥ (by rw [Ideal.mul_bot, h, Ideal.bot_mul]))
  have h𝔣 : 𝔣 ≠ ⊥ := fun h => hvdvd (Dvd.intro ⊥ (by
    rw [Ideal.mul_bot, h, pow_two, Ideal.mul_bot, Ideal.mul_bot]))
  have hvS : v ∉ AutomorphicForm.GaussTwist.modulusPrimes F 𝔣 := fun hin => hvdvd
    (dvd_trans ((AutomorphicForm.GaussTwist.mem_modulusPrimes F h𝔣 v).mp hin)
      (dvd_mul_of_dvd_right (dvd_pow_self 𝔣 two_ne_zero) N))
  have hsys' : ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsCompact F).U (N * 𝔣 ^ 2)) (heckeGen (𝓞 F) F v) reps :=
    LanglandsTunnell.exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd F (N * 𝔣 ^ 2) v hvdvd
  exact P7RamTwist.isHeckeCosetEigenfunctionAt_gaussTwistFn F ⟨N, hN, fun _ => 0, fun _ => 0⟩ η 𝔣 h𝔣
    hmod v hvS hvdvd hsys' hinv
    (fun g k hk => LanglandsTunnell.fnTwist_gaussSumFn_level_invariant F N hN η 𝔣 h𝔣 hmod hinv g k hk)
    heig

end S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn
end P2MW
export P2MW.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_fnTwist_gaussSumFn (solution)
