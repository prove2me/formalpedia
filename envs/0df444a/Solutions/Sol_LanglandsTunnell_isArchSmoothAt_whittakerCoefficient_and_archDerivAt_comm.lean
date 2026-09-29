-- Prove2me | solution 1 for LanglandsTunnell.isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bf1645eb-f063-5801-a066-cbd6877aee57

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal)

section Surgery

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private theorem glArch_ext {M N : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ w M = archComponent ℚ w N) : M = N := by
  apply Units.ext
  ext i j
  funext v
  obtain rfl : v = w := Subsingleton.elim _ _
  exact congrArg (fun P : GL (Fin 2) v.Completion => (P : Matrix (Fin 2) (Fin 2) v.Completion) i j) h

private theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt hw m) = archGLIncl ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl ℚ _

private theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem archComponent_glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    archComponent ℚ w (glArch (𝓞 ℚ) ℚ (archRealGLAt hw m))
      = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

private def finUnipotent (x : AdeleRing (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) ((0 : InfiniteAdeleRing ℚ), x.2)

private theorem glArch_finUnipotent (x : AdeleRing (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (finUnipotent x) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 x) = unipotentGL2 x.2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_finUnipotent (x : AdeleRing (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (finUnipotent x) = unipotentGL2 x.2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def realCoord (x : AdeleRing (𝓞 ℚ) ℚ) : ℝ := ringEquivRealOfIsReal hw (x.1 w)

private theorem archComponent_glArch_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    archComponent ℚ w (glArch (𝓞 ℚ) ℚ (unipotentGL2 x))
      = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (unipotentGL2 (realCoord hw x)) := by
  apply Units.ext
  ext i j : 1
  rw [glEquivOfRingEquiv_apply_entry]
  fin_cases i <;> fin_cases j
  · show ((1 : AdeleRing (𝓞 ℚ) ℚ).1) w = (ringEquivRealOfIsReal hw).symm 1
    rw [map_one]; rfl
  · show (x.1) w = (ringEquivRealOfIsReal hw).symm (realCoord hw x)
    exact ((ringEquivRealOfIsReal hw).symm_apply_apply _).symm
  · show ((0 : AdeleRing (𝓞 ℚ) ℚ).1) w = (ringEquivRealOfIsReal hw).symm 0
    rw [map_zero]; rfl
  · show ((1 : AdeleRing (𝓞 ℚ) ℚ).1) w = (ringEquivRealOfIsReal hw).symm 1
    rw [map_one]; rfl

private theorem unipotentGL2_eq_archRealGLAt_mul (x : AdeleRing (𝓞 ℚ) ℚ) :
    unipotentGL2 x = archRealGLAt hw (unipotentGL2 (realCoord hw x))
      * finUnipotent x := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, glArch_finUnipotent, mul_one]
    apply glArch_ext (w := w)
    rw [archComponent_glArch_unipotentGL2 hw, archComponent_glArch_archRealGLAt]
  · rw [map_mul, glFin_archRealGLAt, one_mul, glFin_unipotentGL2, glFin_finUnipotent]

private theorem glArch_archRealProjAt_inv_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, inv_mul_eq_one]
  apply glArch_ext (w := w)
  rw [archComponent_glArch_archRealGLAt]
  apply Units.ext
  ext i j : 1
  rw [glEquivOfRingEquiv_apply_entry]
  show (ringEquivRealOfIsReal hw).symm (ringEquivRealOfIsReal hw
      ((archComponent ℚ w (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) w.Completion) i j))
    = (archComponent ℚ w (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

private theorem archRealGLAt_mul_archRealLiftAt (m : GL (Fin 2) ℝ) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archRealGLAt hw m * archRealLiftAt hw e =
      archRealLiftAt hw (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hm h
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem unipotentGL2_mul_chart (x : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    unipotentGL2 x * (g * archRealLiftAt hw e)
      = finUnipotent x
          * ((archRealGLAt hw (archRealProjAt hw g))⁻¹ * g)
          * archRealLiftAt hw (Matrix.of.symm
              (((unipotentGL2 (realCoord hw x) * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
                * Matrix.of e)) := by
  set p := archRealProjAt hw g with hp
  set g₀ := (archRealGLAt hw p)⁻¹ * g with hg₀
  have hg : g = archRealGLAt hw p * g₀ := by rw [hg₀, mul_inv_cancel_left]
  have h0 : glArch (𝓞 ℚ) ℚ g₀ = 1 := glArch_archRealProjAt_inv_mul hw g
  have hf : glArch (𝓞 ℚ) ℚ (finUnipotent x) = 1 :=
    glArch_finUnipotent x
  calc unipotentGL2 x * (g * archRealLiftAt hw e)
      = archRealGLAt hw (unipotentGL2 (realCoord hw x))
          * finUnipotent x
          * (archRealGLAt hw p * g₀ * archRealLiftAt hw e) := by
        rw [unipotentGL2_eq_archRealGLAt_mul hw x, ← hg]
    _ = finUnipotent x
          * (archRealGLAt hw (unipotentGL2 (realCoord hw x)) * archRealGLAt hw p) * g₀ * archRealLiftAt hw e := by
        rw [archRealGLAt_mul_comm_of_glArch_eq_one hw _ hf]; simp only [mul_assoc]
    _ = finUnipotent x * g₀
          * (archRealGLAt hw (unipotentGL2 (realCoord hw x) * p) * archRealLiftAt hw e) := by
        rw [← map_mul, mul_assoc (finUnipotent x), archRealGLAt_mul_comm_of_glArch_eq_one hw _ h0]
        simp only [mul_assoc]
    _ = _ := by rw [archRealGLAt_mul_archRealLiftAt hw _ he]

end Surgery

section Factorization

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private theorem continuous_unipotentGL2_val :
    Continuous fun y : AdeleRing (𝓞 ℚ) ℚ =>
      ((unipotentGL2 y : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop

private theorem continuous_unipotentGL2_adele :
    Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => (unipotentGL2 y : AdelicGL2 (𝓞 ℚ) ℚ) := by
  have hinv : ∀ y : AdeleRing (𝓞 ℚ) ℚ, (unipotentGL2 y : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ = unipotentGL2 (-y) := fun y =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  refine Units.continuous_iff.2 ⟨continuous_unipotentGL2_val, ?_⟩
  simp only [hinv]
  exact continuous_unipotentGL2_val.comp continuous_neg

private theorem finUnipotent_mem (x : AdeleRing (𝓞 ℚ) ℚ) : finUnipotent x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff (F := ℚ) _).2 (glArch_finUnipotent x)

private theorem continuous_realCoord : Continuous (realCoord hw) := by
  have h : Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => x.1 w := (continuous_apply w).comp continuous_fst
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp h

private theorem measurable_realCoord :
    @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) _ (realCoord hw) := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact (continuous_realCoord hw).measurable

private theorem exists_bound_realCoord :
    ∃ R : ℝ, ∀ x ∈ NumberField.AdelicBox.adelicBox ℚ, |realCoord hw x| ≤ R := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn (continuous_realCoord hw).continuousOn
  exact ⟨R, fun x hx => by simpa only [Real.norm_eq_abs] using hR x (hsub hx)⟩

open scoped Classical in

private def pieceIndex {X : Type} {N : ℕ} (W : Fin N → Set X) (i₀ : Fin N) : List (Fin N) → X → Fin N
  | [] => fun _ => i₀
  | i :: l => (W i).piecewise (fun _ => i) (pieceIndex W i₀ l)

private theorem measurable_pieceIndex {X : Type} [MeasurableSpace X] {N : ℕ} {W : Fin N → Set X}
    (hW : ∀ i, MeasurableSet (W i)) (i₀ : Fin N) : ∀ l : List (Fin N), Measurable (pieceIndex W i₀ l)
  | [] => measurable_const
  | i :: l => by
    rw [pieceIndex]
    exact Measurable.piecewise (hW i) measurable_const (measurable_pieceIndex hW i₀ l)

private theorem mem_pieceIndex {X : Type} {N : ℕ} (W : Fin N → Set X) (i₀ : Fin N) :
    ∀ (l : List (Fin N)) (x : X), x ∈ W (pieceIndex W i₀ l x) ∨ ∀ i ∈ l, x ∉ W i
  | [], _ => Or.inr fun i hi => by simp at hi
  | i :: l, x => by
    simp only [pieceIndex, Set.piecewise]
    by_cases hx : x ∈ W i
    · rw [if_pos hx]
      exact Or.inl hx
    · rw [if_neg hx]
      rcases mem_pieceIndex W i₀ l x with h | h
      · exact Or.inl h
      · refine Or.inr fun j hj => ?_
        rcases List.mem_cons.1 hj with rfl | hj
        · exact hx
        · exact h j hj

private def pairAd (δ : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ := ((0 : InfiniteAdeleRing ℚ), δ)

private theorem finUnipotent_eq_pairAd (x : AdeleRing (𝓞 ℚ) ℚ) : finUnipotent x = finUnipotent (pairAd x.2) := by
  simp only [finUnipotent, pairAd]

private theorem finUnipotent_pairAd_zero : finUnipotent (pairAd 0) = 1 := by
  simp only [finUnipotent, pairAd]
  exact unipotentGL2_zero

private theorem finUnipotent_pairAd_add (a b : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :
    finUnipotent (pairAd (a + b)) = finUnipotent (pairAd a) * finUnipotent (pairAd b) := by
  have h : (((0 : InfiniteAdeleRing ℚ), a + b) : InfiniteAdeleRing ℚ × IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)
      = ((0 : InfiniteAdeleRing ℚ), a) + ((0 : InfiniteAdeleRing ℚ), b) := by
    ext <;> simp
  simp only [finUnipotent, pairAd]
  rw [← unipotentGL2_add]
  exact congrArg _ h

private theorem continuous_finUnipotent_pairAd : Continuous fun δ => finUnipotent (pairAd δ) := by
  have h : Continuous fun δ : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ =>
      (((0 : InfiniteAdeleRing ℚ), δ) : AdeleRing (𝓞 ℚ) ℚ) :=
    continuous_const.prodMk continuous_id
  simp only [finUnipotent, pairAd]
  exact continuous_unipotentGL2_adele.comp h

private theorem exists_factorization {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : IsArchSmoothAt hw φ)
    (hKf : IsKfSmooth ℚ φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (N : ℕ) (G : Fin N → (Fin 2 → Fin 2 → ℝ) → ℂ) (c : AdeleRing (𝓞 ℚ) ℚ → Fin N),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (G i) {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0}) ∧
      @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) _ c ∧
      ∀ x ∈ NumberField.AdelicBox.adelicBox ℚ, ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
        φ (unipotentGL2 x * (g * archRealLiftAt hw e)) =
          G (c x) (Matrix.of.symm
            (((unipotentGL2 (realCoord hw x) * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
              * Matrix.of e)) := by

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, (archRealGLAt hw (archRealProjAt hw g))⁻¹ * g = g₀ := ⟨_, rfl⟩
  have hg₀mem : g₀ ∈ finiteAdelicGL2Subgroup ℚ := by
    rw [← hg₀]
    exact (mem_finiteAdelicGL2Subgroup_iff (F := ℚ) _).2 (glArch_archRealProjAt_inv_mul hw g)

  obtain ⟨S, hSopen, hS1, hSstab⟩ : ∃ S : Set (finiteAdelicGL2Subgroup ℚ),
      IsOpen S ∧ (1 : finiteAdelicGL2Subgroup ℚ) ∈ S ∧
        ∀ k ∈ S, ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, φ (Y * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = φ Y :=
    ⟨_, hKf, SetLike.mem_coe.2 (Subgroup.one_mem _), fun k hk Y =>
      congrArg (fun f : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 ℚ) ℚ) ℂ =>
        FLT.SmoothVectors.RightTranslationFn.toFun f Y) (MulAction.mem_stabilizer_iff.1 (SetLike.mem_coe.1 hk))⟩

  obtain ⟨kf, hkf_cont, hkf⟩ : ∃ kf : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ → finiteAdelicGL2Subgroup ℚ,
      Continuous kf ∧ ∀ δ, (kf δ : AdelicGL2 (𝓞 ℚ) ℚ) = g₀⁻¹ * finUnipotent (pairAd δ) * g₀ :=
    ⟨fun δ => ⟨g₀⁻¹ * finUnipotent (pairAd δ) * g₀,
        (finiteAdelicGL2Subgroup ℚ).mul_mem
          ((finiteAdelicGL2Subgroup ℚ).mul_mem ((finiteAdelicGL2Subgroup ℚ).inv_mem hg₀mem) (finUnipotent_mem _))
          hg₀mem⟩,
      ((continuous_const.mul continuous_finUnipotent_pairAd).mul continuous_const).subtype_mk _, fun _ => rfl⟩
  have hkf_zero : kf 0 ∈ S := by
    have h1 : kf 0 = 1 := Subtype.ext (by simp [hkf, finUnipotent_pairAd_zero])
    rw [h1]
    exact hS1

  have hV : IsOpen (kf ⁻¹' S) := hSopen.preimage hkf_cont
  obtain ⟨t, -, ht⟩ := (NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ).elim_nhds_subcover
    (fun o => (fun y => y - o) ⁻¹' (kf ⁻¹' S)) fun o _ =>
      (hV.preimage (continuous_id.sub continuous_const)).mem_nhds (by
        show kf (o - o) ∈ S
        rw [sub_self]
        exact hkf_zero)
  obtain ⟨q, hq⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 ℚ) ℚ 0
  obtain ⟨o₀, ho₀, -⟩ := Set.mem_iUnion₂.1 (ht hq)

  obtain ⟨reps, hreps⟩ : ∃ reps : Fin t.card → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ,
      ∀ o (ho : o ∈ t), reps (t.equivFin ⟨o, ho⟩) = o :=
    ⟨fun i => ((t.equivFin.symm i : t) : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ), fun o ho => by simp⟩
  obtain ⟨W, hWopen, hW⟩ : ∃ W : Fin t.card → Set (AdeleRing (𝓞 ℚ) ℚ), (∀ i, IsOpen (W i)) ∧
      ∀ i (x : AdeleRing (𝓞 ℚ) ℚ), x ∈ W i ↔ kf (x.2 - reps i) ∈ S :=
    ⟨fun i => (fun x : AdeleRing (𝓞 ℚ) ℚ => x.2 - reps i) ⁻¹' (kf ⁻¹' S),
      fun i => hV.preimage (continuous_snd.sub continuous_const), fun _ _ => Iff.rfl⟩
  refine ⟨t.card, fun i e' => φ (finUnipotent (pairAd (reps i)) * g₀ * archRealLiftAt hw e'),
    pieceIndex W (t.equivFin ⟨o₀, ho₀⟩) (List.finRange t.card), fun i => hφ _, ?_, ?_⟩
  · letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
    exact measurable_pieceIndex (fun i => (hWopen i).measurableSet) _ _
  · intro x hx e he
    obtain ⟨-, hx2⟩ := hx

    have hxW : x ∈ W (pieceIndex W (t.equivFin ⟨o₀, ho₀⟩) (List.finRange t.card) x) := by
      obtain ⟨o, ho, hxo⟩ := Set.mem_iUnion₂.1 (ht hx2)
      have hxWo : x ∈ W (t.equivFin ⟨o, ho⟩) := by
        rw [hW, hreps]
        exact hxo
      rcases mem_pieceIndex W (t.equivFin ⟨o₀, ho₀⟩) (List.finRange t.card) x with h | h
      · exact h
      · exact absurd hxWo (h _ (List.mem_finRange _))
    obtain ⟨j, hj⟩ : ∃ j, pieceIndex W (t.equivFin ⟨o₀, ho₀⟩) (List.finRange t.card) x = j := ⟨_, rfl⟩
    rw [hj] at hxW ⊢
    have hk : kf (x.2 - reps j) ∈ S := (hW j x).1 hxW
    have hk1 : glArch (𝓞 ℚ) ℚ (kf (x.2 - reps j) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
      (mem_finiteAdelicGL2Subgroup_iff (F := ℚ) _).1 (kf (x.2 - reps j)).2

    have hsplit : finUnipotent x = finUnipotent (pairAd (reps j)) * finUnipotent (pairAd (x.2 - reps j)) := by
      rw [finUnipotent_eq_pairAd x, ← finUnipotent_pairAd_add, add_sub_cancel]
    have hconj : finUnipotent (pairAd (x.2 - reps j)) * g₀ = g₀ * (kf (x.2 - reps j) : AdelicGL2 (𝓞 ℚ) ℚ) := by
      rw [hkf, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have hcomm : (kf (x.2 - reps j) : AdelicGL2 (𝓞 ℚ) ℚ) * archRealLiftAt hw (Matrix.of.symm
          (((unipotentGL2 (realCoord hw x) * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
            * Matrix.of e))
        = archRealLiftAt hw (Matrix.of.symm
            (((unipotentGL2 (realCoord hw x) * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
              * Matrix.of e)) * (kf (x.2 - reps j) : AdelicGL2 (𝓞 ℚ) ℚ) :=
      (archRealLiftAt_mul_comm_of_glArch_eq_one hw _ hk1).symm
    rw [unipotentGL2_mul_chart hw x g he, hg₀, hsplit, mul_assoc (finUnipotent (pairAd (reps j))), hconj,
      ← mul_assoc, mul_assoc (finUnipotent (pairAd (reps j)) * g₀), hcomm, ← mul_assoc]
    exact hSstab _ hk _

end Factorization

section Analytic

open MeasureTheory Metric Set
open scoped Topology

private abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

private abbrev tcDetSet : Set Ent := {e : Ent | (Matrix.of e).det ≠ 0}

private theorem tc_isOpen_detSet : IsOpen tcDetSet := by
  have h : Continuous fun e : Ent => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

private def tcMulLin (a : Ent) : Ent →ₗ[ℝ] Ent where
  toFun e := Matrix.of.symm (Matrix.of a * Matrix.of e)
  map_add' e₁ e₂ := by
    show Matrix.of.symm (Matrix.of a * (Matrix.of e₁ + Matrix.of e₂)) =
      Matrix.of.symm (Matrix.of a * Matrix.of e₁) + Matrix.of.symm (Matrix.of a * Matrix.of e₂)
    rw [Matrix.mul_add]
    rfl
  map_smul' t e := by
    show Matrix.of.symm (Matrix.of a * (t • Matrix.of e)) = t • Matrix.of.symm (Matrix.of a * Matrix.of e)
    rw [Matrix.mul_smul]
    rfl

private def tcMulL (a : Ent) : Ent →L[ℝ] Ent := LinearMap.toContinuousLinearMap (tcMulLin a)

private theorem tcMulL_apply (a e : Ent) : tcMulL a e = Matrix.of.symm (Matrix.of a * Matrix.of e) := rfl

private def tcMulLL : Ent →ₗ[ℝ] (Ent →L[ℝ] Ent) where
  toFun := tcMulL
  map_add' a₁ a₂ := by
    refine ContinuousLinearMap.ext fun e => ?_
    show Matrix.of.symm ((Matrix.of a₁ + Matrix.of a₂) * Matrix.of e) =
      Matrix.of.symm (Matrix.of a₁ * Matrix.of e) + Matrix.of.symm (Matrix.of a₂ * Matrix.of e)
    rw [Matrix.add_mul]
    rfl
  map_smul' t a := by
    refine ContinuousLinearMap.ext fun e => ?_
    show Matrix.of.symm ((t • Matrix.of a) * Matrix.of e) = t • Matrix.of.symm (Matrix.of a * Matrix.of e)
    rw [Matrix.smul_mul]
    rfl

private theorem tc_continuous_mulL : Continuous (tcMulL : Ent → Ent →L[ℝ] Ent) :=
  tcMulLL.continuous_of_finiteDimensional

private theorem tc_mulL_mem_detSet {a : Ent} (ha : (Matrix.of a).det ≠ 0) {e : Ent} (he : e ∈ tcDetSet) :
    tcMulL a e ∈ tcDetSet := by
  show (Matrix.of (Matrix.of.symm (Matrix.of a * Matrix.of e))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_mul]
  exact mul_ne_zero ha he

section Engine

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private structure TcFamily (F : X → Ent → Y) : Prop where
  smooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (F x) tcDetSet
  meas : ∀ m : ℕ, ∀ e ∈ tcDetSet, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (F x) e) ν
  bound : ∀ e₀ ∈ tcDetSet, ∀ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ball e₀ ρ ⊆ tcDetSet ∧
    ∃ C : ℝ, ∀ᵐ x ∂ν, ∀ e ∈ ball e₀ ρ, ‖iteratedFDeriv ℝ m (F x) e‖ ≤ C

variable {ν}

private theorem tc_aesm_of_zero {g : X → Ent → Y} {e : Ent}
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (g x) e) ν) :
    AEStronglyMeasurable (fun x => g x e) ν := by
  have hfun : (fun x => g x e) =
      fun x => (continuousMultilinearCurryFin0 ℝ Ent Y) (iteratedFDeriv ℝ 0 (g x) e) := by
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryFin0 ℝ Ent Y).continuous.comp_aestronglyMeasurable h

private theorem tc_aesm_fderiv_order {F : X → Ent → Y} (hF : TcFamily ν F) (m : ℕ) {e : Ent} (he : e ∈ tcDetSet) :
    AEStronglyMeasurable (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) ν := by
  have hfun : (fun x => iteratedFDeriv ℝ m (fderiv ℝ (F x)) e) =
      fun x => (continuousMultilinearCurryRightEquiv' ℝ m Ent Y) (iteratedFDeriv ℝ (m + 1) (F x) e) := by
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  rw [hfun]
  exact (continuousMultilinearCurryRightEquiv' ℝ m Ent Y).continuous.comp_aestronglyMeasurable
    (hF.meas (m + 1) e he)

private theorem tc_norm_fderiv_eq (f : Ent → Y) (e : Ent) : ‖fderiv ℝ f e‖ = ‖iteratedFDeriv ℝ 1 f e‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]

private theorem tc_differentiableAt {F : X → Ent → Y} (hF : TcFamily ν F) (x : X) {e : Ent} (he : e ∈ tcDetSet) :
    DifferentiableAt ℝ (F x) e :=
  ((hF.smooth x).differentiableOn (by simp) e he).differentiableAt (tc_isOpen_detSet.mem_nhds he)

private theorem tc_integrable_fderiv [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) :
    Integrable (fun x => fderiv ℝ (F x) e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 1
  refine Integrable.of_bound (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀)) C (hC.mono fun x hx => ?_)
  rw [tc_norm_fderiv_eq]
  exact hx e₀ (mem_ball_self hρ)

private theorem tc_integrable_zero [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) : Integrable (fun x => F x e₀) ν := by
  obtain ⟨ρ, hρ, -, C, hC⟩ := hF.bound e₀ he₀ 0
  refine Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C (hC.mono fun x hx => ?_)
  have h0 := hx e₀ (mem_ball_self hρ)
  rwa [norm_iteratedFDeriv_zero] at h0

private theorem tc_hasFDerivAt_integral [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) {e₀ : Ent}
    (he₀ : e₀ ∈ tcDetSet) :
    HasFDerivAt (fun e => ∫ x, F x e ∂ν) (∫ x, fderiv ℝ (F x) e₀ ∂ν) e₀ := by
  obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ 1
  obtain ⟨ρ₀, hρ₀, -, C₀, hC₀⟩ := hF.bound e₀ he₀ 0
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun e x => F x e)
    (F' := fun e x => fderiv ℝ (F x) e) (x₀ := e₀) (bound := fun _ => C) (ball_mem_nhds e₀ hρ)
    (Filter.eventually_of_mem (tc_isOpen_detSet.mem_nhds he₀) fun e he => tc_aesm_of_zero (hF.meas 0 e he))
    (Integrable.of_bound (tc_aesm_of_zero (hF.meas 0 e₀ he₀)) C₀ (hC₀.mono fun x hx => by
      have h0 := hx e₀ (mem_ball_self hρ₀)
      rwa [norm_iteratedFDeriv_zero] at h0))
    (tc_aesm_of_zero (tc_aesm_fderiv_order hF 0 he₀))
    (hC.mono fun x hx e he => by rw [tc_norm_fderiv_eq]; exact hx e he)
    (integrable_const C)
    (Filter.Eventually.of_forall fun x e he => (tc_differentiableAt hF x (hball he)).hasFDerivAt)
  exact h

private theorem tc_contDiffOn_integral_nat [IsFiniteMeasure ν] (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : X → Ent → Z),
      TcFamily ν F → ContDiffOn ℝ n (fun e => ∫ x, F x e ∂ν) tcDetSet := by
  induction n with
  | zero =>
    intro Z _ _ F hF
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun e he => (tc_hasFDerivAt_integral hF he).continuousAt.continuousWithinAt
  | succ n ih =>
    intro Z _ _ F hF
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen tc_isOpen_detSet]
    refine ⟨fun e he => (tc_hasFDerivAt_integral hF he).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hF' : TcFamily ν fun x => fderiv ℝ (F x) :=
      { smooth := fun x => (hF.smooth x).fderiv_of_isOpen tc_isOpen_detSet (by simp)
        meas := fun m e he => tc_aesm_fderiv_order hF m he
        bound := fun e₀ he₀ m => by
          obtain ⟨ρ, hρ, hball, C, hC⟩ := hF.bound e₀ he₀ (m + 1)
          exact ⟨ρ, hρ, hball, C, hC.mono fun x hx e he => by rw [norm_iteratedFDeriv_fderiv]; exact hx e he⟩ }
    exact (ih _ hF').congr fun e he => (tc_hasFDerivAt_integral hF he).fderiv

private theorem tc_contDiffOn_integral [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ∫ x, F x e ∂ν) tcDetSet :=
  contDiffOn_infty.mpr fun n => tc_contDiffOn_integral_nat n F hF

private theorem tc_deriv_integral_comp [IsFiniteMeasure ν] {F : X → Ent → Y} (hF : TcFamily ν F) (γ : ℝ → Ent)
    (hγ : DifferentiableAt ℝ γ 0) (h0 : γ 0 ∈ tcDetSet) :
    deriv (fun t : ℝ => ∫ x, F x (γ t) ∂ν) 0 = ∫ x, deriv (fun t : ℝ => F x (γ t)) 0 ∂ν := by
  have hγ' := hγ.hasDerivAt
  have h1 := (tc_hasFDerivAt_integral hF h0).comp_hasDerivAt (0 : ℝ) hγ'
  have h2 : ∀ x, deriv (fun t : ℝ => F x (γ t)) 0 = fderiv ℝ (F x) (γ 0) (deriv γ 0) := fun x =>
    ((tc_differentiableAt hF x h0).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ').deriv
  change deriv ((fun e => ∫ x, F x e ∂ν) ∘ γ) 0 = _
  rw [h1.deriv, ContinuousLinearMap.integral_apply (tc_integrable_fderiv hF h0)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (h2 x).symm)

end Engine

section Bridge

variable {X : Type} [MeasurableSpace X] {ν : Measure X}
variable {N : ℕ} {G : Fin N → Ent → ℂ}

private theorem tc_iteratedFDeriv_smul_comp (hG : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (G i) tcDetSet) (i : Fin N)
    {a : Ent} (ha : (Matrix.of a).det ≠ 0) (ξ : ℂ) (m : ℕ) {e : Ent} (he : e ∈ tcDetSet) :
    iteratedFDeriv ℝ m (fun e' => ξ • (G i ∘ ⇑(tcMulL a)) e') e =
      ξ • (iteratedFDerivWithin ℝ m (G i) tcDetSet (tcMulL a e)).compContinuousLinearMap
        fun _ => tcMulL a := by
  show iteratedFDeriv ℝ m (ξ • (G i ∘ ⇑(tcMulL a))) e = _
  have hT : IsOpen (⇑(tcMulL a) ⁻¹' tcDetSet) := tc_isOpen_detSet.preimage (tcMulL a).continuous
  have heT : e ∈ ⇑(tcMulL a) ⁻¹' tcDetSet := tc_mulL_mem_detSet ha he
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (G i ∘ ⇑(tcMulL a)) (⇑(tcMulL a) ⁻¹' tcDetSet) :=
    (hG i).comp (tcMulL a).contDiff.contDiffOn fun _ hx => hx
  rw [← iteratedFDerivWithin_of_isOpen m hT heT,
    iteratedFDerivWithin_const_smul_apply ((hg e heT).of_le (by exact_mod_cast le_top)) hT.uniqueDiffOn heT,
    (tcMulL a).iteratedFDerivWithin_comp_right (hG i) tc_isOpen_detSet.uniqueDiffOn hT.uniqueDiffOn heT
      (by exact_mod_cast le_top)]

private theorem tc_continuous_closedForm (hG : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (G i) tcDetSet) (i : Fin N)
    {a : ℝ → Ent} (ha : Continuous a) (hadet : ∀ t, (Matrix.of (a t)).det ≠ 0) (m : ℕ) {e : Ent}
    (he : e ∈ tcDetSet) :
    Continuous fun t : ℝ => (iteratedFDerivWithin ℝ m (G i) tcDetSet (tcMulL (a t) e)).compContinuousLinearMap
      fun _ : Fin m => tcMulL (a t) := by
  have hL : Continuous fun t : ℝ => tcMulL (a t) := tc_continuous_mulL.comp ha
  have hinner : Continuous fun t : ℝ => iteratedFDerivWithin ℝ m (G i) tcDetSet (tcMulL (a t) e) :=
    ((hG i).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) tc_isOpen_detSet.uniqueDiffOn).comp_continuous
      (hL.clm_apply continuous_const) fun t => tc_mulL_mem_detSet (hadet t) he
  have houter : Continuous fun t : ℝ =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin m => Ent)
        (fun _ : Fin m => Ent) ℂ fun _ : Fin m => tcMulL (a t) :=
    (ContinuousMultilinearMap.coe_continuous (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin m => Ent) (fun _ : Fin m => Ent) ℂ)).comp (continuous_pi fun _ => hL)
  have h := houter.clm_apply hinner
  simpa only [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply] using h

private theorem tc_aesm_of_finite {Z : Type} [NormedAddCommGroup Z] (Θ : Fin N → ℝ → Z)
    (hΘ : ∀ i, Continuous (Θ i)) {c : X → Fin N} (hc : Measurable c) {r : X → ℝ} (hr : Measurable r) :
    AEStronglyMeasurable (fun x => Θ (c x) (r x)) ν := by
  have hfun : (fun x => Θ (c x) (r x)) =
      fun x => ∑ i : Fin N, (c ⁻¹' {i}).indicator (fun y => Θ i (r y)) x := by
    funext x
    rw [Finset.sum_eq_single (c x)]
    · rw [indicator_of_mem (by simp)]
    · intro i _ hi
      exact indicator_of_notMem (by simpa using hi.symm) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hfun]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    ((hΘ i).comp_aestronglyMeasurable hr.aestronglyMeasurable).indicator (hc (measurableSet_singleton i))

private theorem tc_family (hG : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (G i) tcDetSet) {c : X → Fin N} (hc : Measurable c)
    {r : X → ℝ} (hr : Measurable r) {R : ℝ} (hrb : ∀ᵐ x ∂ν, |r x| ≤ R) {a : ℝ → Ent} (ha : Continuous a)
    (hadet : ∀ t, (Matrix.of (a t)).det ≠ 0) {χ : X → ℂ} (hχ : AEStronglyMeasurable χ ν) {Cχ : ℝ}
    (hχb : ∀ᵐ x ∂ν, ‖χ x‖ ≤ Cχ) :
    TcFamily ν fun x e => χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) e where
  smooth x := by
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (G (c x) ∘ ⇑(tcMulL (a (r x)))) tcDetSet :=
      (hG (c x)).comp (tcMulL _).contDiff.contDiffOn fun _ hy => tc_mulL_mem_detSet (hadet _) hy
    exact h.const_smul (χ x)
  meas m e he := by
    have hfun : (fun x => iteratedFDeriv ℝ m (fun e' => χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) e') e) = fun x =>
        χ x • (fun i t => (iteratedFDerivWithin ℝ m (G i) tcDetSet (tcMulL (a t) e)).compContinuousLinearMap
          fun _ : Fin m => tcMulL (a t)) (c x) (r x) := by
      funext x
      exact tc_iteratedFDeriv_smul_comp hG (c x) (hadet (r x)) (χ x) m he
    rw [hfun]
    exact hχ.smul (tc_aesm_of_finite _ (fun i => tc_continuous_closedForm hG i ha hadet m he) hc hr)
  bound e₀ he₀ m := by
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp tc_isOpen_detSet e₀ he₀
    have hcb : closedBall e₀ (ε / 2) ⊆ tcDetSet := (closedBall_subset_ball (by linarith)).trans hεS

    have hK : IsCompact ((fun p : ℝ × Ent => tcMulL (a p.1) p.2) '' (Icc (-R) R ×ˢ closedBall e₀ (ε / 2))) :=
      (isCompact_Icc.prod (isCompact_closedBall e₀ (ε / 2))).image
        ((tc_continuous_mulL.comp (ha.comp continuous_fst)).clm_apply continuous_snd)
    have hKS : (fun p : ℝ × Ent => tcMulL (a p.1) p.2) '' (Icc (-R) R ×ˢ closedBall e₀ (ε / 2)) ⊆ tcDetSet := by
      rintro _ ⟨p, hp, rfl⟩
      exact tc_mulL_mem_detSet (hadet _) (hcb hp.2)
    choose Cg hCg using fun i : Fin N => hK.exists_bound_of_continuousOn
      (((hG i).continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
        tc_isOpen_detSet.uniqueDiffOn).mono hKS)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R)
      (tc_continuous_mulL.comp ha).continuousOn
    refine ⟨ε / 2, by positivity, ball_subset_closedBall.trans hcb, Cχ * ((∑ i, |Cg i|) * M ^ m), ?_⟩
    filter_upwards [hrb, hχb] with x hxR hxχ
    intro e he
    rw [tc_iteratedFDeriv_smul_comp hG (c x) (hadet (r x)) (χ x) m (hcb (ball_subset_closedBall he)), norm_smul]
    have hxI : r x ∈ Icc (-R) R := abs_le.mp hxR
    have hMx : ‖tcMulL (a (r x))‖ ≤ M := hM (r x) hxI
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hMx
    have hmem : tcMulL (a (r x)) e ∈
        (fun p : ℝ × Ent => tcMulL (a p.1) p.2) '' (Icc (-R) R ×ˢ closedBall e₀ (ε / 2)) :=
      ⟨(r x, e), ⟨hxI, ball_subset_closedBall he⟩, rfl⟩
    have hCx : ‖iteratedFDerivWithin ℝ m (G (c x)) tcDetSet (tcMulL (a (r x)) e)‖ ≤ ∑ i, |Cg i| :=
      (hCg (c x) _ hmem).trans ((le_abs_self _).trans
        (Finset.single_le_sum (fun i _ => abs_nonneg (Cg i)) (Finset.mem_univ (c x))))
    have hcomp : ‖(iteratedFDerivWithin ℝ m (G (c x)) tcDetSet (tcMulL (a (r x)) e)).compContinuousLinearMap
        fun _ : Fin m => tcMulL (a (r x))‖ ≤ (∑ i, |Cg i|) * M ^ m := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul hCx (pow_le_pow_left₀ (norm_nonneg _) hMx m) (by positivity) (by positivity)
    have hχ0 : 0 ≤ Cχ := (norm_nonneg _).trans hxχ
    exact mul_le_mul hxχ hcomp (norm_nonneg _) hχ0

end Bridge

private theorem contDiffOn_integral_of_factorization
    {X : Type} [MeasurableSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure ν]
    {N : ℕ} (G : Fin N → (Fin 2 → Fin 2 → ℝ) → ℂ)
    (hG : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (G i) {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0})
    (c : X → Fin N) (hc : Measurable c)
    (r : X → ℝ) (hr : Measurable r) (hrb : ∃ R : ℝ, ∀ᵐ x ∂ν, |r x| ≤ R)
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hA : Continuous A) (hAdet : ∀ t : ℝ, (A t).det ≠ 0)
    (χ : X → ℂ) (hχ : MeasureTheory.AEStronglyMeasurable χ ν) (hχb : ∃ C : ℝ, ∀ᵐ x ∂ν, ‖χ x‖ ≤ C)
    (Ψ : X → (Fin 2 → Fin 2 → ℝ) → ℂ)
    (hΨ : ∀ᵐ x ∂ν, ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
      Ψ x e = G (c x) (Matrix.of.symm (A (r x) * Matrix.of e))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ∫ x, Ψ x e * χ x ∂ν)
        {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} ∧
      (∀ γ : ℝ → (Fin 2 → Fin 2 → ℝ), DifferentiableAt ℝ γ 0 → (Matrix.of (γ 0)).det ≠ 0 →
        deriv (fun t : ℝ => ∫ x, Ψ x (γ t) * χ x ∂ν) 0 = ∫ x, deriv (fun t : ℝ => Ψ x (γ t)) 0 * χ x ∂ν) ∧
      ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
        MeasureTheory.Integrable (fun x => Ψ x e * χ x) ν := by
  obtain ⟨R, hrb⟩ := hrb
  obtain ⟨Cχ, hχb⟩ := hχb

  set a : ℝ → Ent := fun t => Matrix.of.symm (A t) with ha_def
  have ha : Continuous a := hA
  have hadet : ∀ t, (Matrix.of (a t)).det ≠ 0 := fun t => by
    simp only [ha_def, Equiv.apply_symm_apply]
    exact hAdet t
  have hfam := tc_family hG hc hr hrb ha hadet hχ hχb

  have hpt : ∀ᵐ x ∂ν, ∀ e ∈ tcDetSet, Ψ x e * χ x = χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) e := by
    filter_upwards [hΨ] with x hx
    intro e he
    rw [hx e he, mul_comm, smul_eq_mul]
    simp only [Function.comp_apply, tcMulL_apply, ha_def, Equiv.apply_symm_apply]
  have hint : ∀ e ∈ tcDetSet, ∫ x, Ψ x e * χ x ∂ν = ∫ x, χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) e ∂ν :=
    fun e he => integral_congr_ae (hpt.mono fun x hx => hx e he)
  refine ⟨(tc_contDiffOn_integral hfam).congr hint, ?_, fun e he =>
    (tc_integrable_zero hfam he).congr (hpt.mono fun x hx => (hx e he).symm)⟩
  intro γ hγ h0
  have h0' : γ 0 ∈ tcDetSet := h0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ tcDetSet := hγ.continuousAt.preimage_mem_nhds (tc_isOpen_detSet.mem_nhds h0')
  have hL : deriv (fun t : ℝ => ∫ x, Ψ x (γ t) * χ x ∂ν) 0 =
      deriv (fun t : ℝ => ∫ x, χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) (γ t) ∂ν) 0 :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun t ht => hint (γ t) ht)
  have hx : ∀ᵐ x ∂ν, deriv (fun t : ℝ => χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) (γ t)) 0 =
      deriv (fun t : ℝ => Ψ x (γ t)) 0 * χ x := by
    filter_upwards [hpt] with x hx
    have h1 : deriv (fun t : ℝ => χ x • (G (c x) ∘ ⇑(tcMulL (a (r x)))) (γ t)) 0 =
        deriv (fun t : ℝ => Ψ x (γ t) * χ x) 0 :=
      Filter.EventuallyEq.deriv_eq (hev.mono fun t ht => (hx (γ t) ht).symm)
    rw [h1, deriv_mul_const_field]
  rw [hL, tc_deriv_integral_comp hfam γ hγ h0']
  exact integral_congr_ae hx

end Analytic

section Assembly

open MeasureTheory

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private abbrev tcPins (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) : CarrierPins ℚ :=
  productionPinsOf ℚ D U gen (NumberField.AdelicBox.adelicBox ℚ)

private theorem isKfSmooth_archDerivAt {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hKf : IsKfSmooth ℚ φ) (d : ArchDir) :
    IsKfSmooth ℚ (archDerivAt hw d φ) := by
  refine Subgroup.isOpen_mono ?_ hKf
  intro k hk
  have hφk : ∀ Y : AdelicGL2 (𝓞 ℚ) ℚ, φ (Y * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = φ Y := fun Y =>
    congrArg (fun f : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 ℚ) ℚ) ℂ =>
      FLT.SmoothVectors.RightTranslationFn.toFun f Y)
      (MulAction.mem_stabilizer_iff.1 hk)
  have hk1 : glArch (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := (mem_finiteAdelicGL2Subgroup_iff (F := ℚ) _).1 k.2
  refine MulAction.mem_stabilizer_iff.2 (FLT.SmoothVectors.RightTranslationFn.ext fun Y => ?_)
  show archDerivAt hw d φ (Y * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = archDerivAt hw d φ Y
  simp only [archDerivAt]
  congr 1
  funext t
  rw [mul_assoc, ← archFlowAt_mul_comm_of_glArch_eq_one hw d t hk1, ← mul_assoc, hφk]

private theorem tc_continuous_unipotentGL2_val_real :
    Continuous fun t : ℝ => ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop

private theorem tc_continuous_flowMatrix (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Continuous fun t : ℝ =>
      ((unipotentGL2 t * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp only [Units.val_mul]
  exact tc_continuous_unipotentGL2_val_real.mul continuous_const

private theorem tc_det_flowMatrix (g : AdelicGL2 (𝓞 ℚ) ℚ) (t : ℝ) :
    (((unipotentGL2 t * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 (unipotentGL2 t * archRealProjAt hw g).isUnit).ne_zero

private theorem tc_continuous_char (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) (α : ℚ) :
    Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)) :=
  hψ.comp (continuous_const.mul continuous_id).neg

private theorem tc_exists_bound_char (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) (α : ℚ) :
    ∃ C : ℝ, ∀ x ∈ NumberField.AdelicBox.adelicBox ℚ, ‖ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))‖ ≤ C := by
  obtain ⟨K, hK, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (tc_continuous_char ψ hψ α).continuousOn
  exact ⟨C, fun x hx => hC x (hsub hx)⟩

private theorem tc_head_applied (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψ : Continuous ψ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ)
    (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (fun e : Fin 2 → Fin 2 → ℝ => ∫ x, φ (unipotentGL2 x * (g * archRealLiftAt hw e))
          * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)) ∂(tcPins D U gen).ν)
        {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} ∧
      (∀ γ : ℝ → (Fin 2 → Fin 2 → ℝ), DifferentiableAt ℝ γ 0 → (Matrix.of (γ 0)).det ≠ 0 →
        deriv (fun t : ℝ => ∫ x, φ (unipotentGL2 x * (g * archRealLiftAt hw (γ t)))
            * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)) ∂(tcPins D U gen).ν) 0 =
          ∫ x, deriv (fun t : ℝ => φ (unipotentGL2 x * (g * archRealLiftAt hw (γ t)))) 0
            * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)) ∂(tcPins D U gen).ν) ∧
      ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
        MeasureTheory.Integrable
          (fun x => φ (unipotentGL2 x * (g * archRealLiftAt hw e)) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)))
          (tcPins D U gen).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := (tcPins D U gen).nS
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : MeasureTheory.IsProbabilityMeasure (tcPins D U gen).ν :=
    NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hbox : ∀ᵐ x ∂(tcPins D U gen).ν, x ∈ NumberField.AdelicBox.adelicBox ℚ :=
    ProbabilityTheory.ae_cond_mem (NumberField.AdelicBox.measurableSet_adelicBox ℚ)
  obtain ⟨N, G, c, hG, hc, hfac⟩ := exists_factorization hw hsm hKf g
  obtain ⟨R, hR⟩ := exists_bound_realCoord hw
  obtain ⟨C, hC⟩ := tc_exists_bound_char ψ hψ α
  exact contDiffOn_integral_of_factorization (tcPins D U gen).ν G hG c hc (realCoord hw) (measurable_realCoord hw)
    ⟨R, hbox.mono fun x hx => hR x hx⟩
    (fun t => ((unipotentGL2 t * archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (tc_continuous_flowMatrix hw g) (tc_det_flowMatrix hw g)
    (fun x => ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))) (tc_continuous_char ψ hψ α).aestronglyMeasurable
    ⟨C, hbox.mono fun x hx => hC x hx⟩
    (fun x e => φ (unipotentGL2 x * (g * archRealLiftAt hw e))) (hbox.mono fun x hx e he => hfac x hx e he)

private theorem tc_isArchSmoothAt_coefficient (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ) (α : ℚ) :
    IsArchSmoothAt hw (whittakerCoefficient ℚ (tcPins D U gen) ψ φ α) := by
  intro g
  obtain ⟨h1, -, -⟩ := tc_head_applied hw D U gen ψ hψ hsm hKf α g
  simp only [whittakerCoefficient]
  exact h1

private theorem tc_integrable_integrand (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψ : Continuous ψ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ)
    (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    MeasureTheory.Integrable (fun x => φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x)))
      (tcPins D U gen).ν := by
  obtain ⟨-, -, h3⟩ := tc_head_applied hw D U gen ψ hψ hsm hKf α g
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have h := h3 _ hdet
  rwa [archRealLiftAt_of_symm_one, mul_one] at h

private theorem tc_archDerivAt_coefficient (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ) (α : ℚ) (d : ArchDir) :
    archDerivAt hw d (whittakerCoefficient ℚ (tcPins D U gen) ψ φ α) =
      whittakerCoefficient ℚ (tcPins D U gen) ψ (archDerivAt hw d φ) α := by
  funext g
  obtain ⟨-, h2, -⟩ := tc_head_applied hw D U gen ψ hψ hsm hKf α g
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero

  have hγ0 : (Matrix.of (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact hdet
  have hflow : ∀ t : ℝ, archFlowAt hw d t = archRealLiftAt hw (Matrix.of.symm
      (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
        * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    intro t
    rw [← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  have h2' := h2 (fun t : ℝ => Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
    * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))
    (hasDerivAt_of_symm_mul_archFlowMatrix _ d).differentiableAt hγ0
  show deriv (fun t : ℝ => whittakerCoefficient ℚ (tcPins D U gen) ψ φ α (g * archFlowAt hw d t)) 0 = _
  simp only [whittakerCoefficient, archDerivAt, hflow]
  rw [h2']
  simp only [mul_assoc]

private theorem tc_archCasimirAt_coefficient (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ) (α : ℚ) :
    archCasimirAt hw (whittakerCoefficient ℚ (tcPins D U gen) ψ φ α) =
      whittakerCoefficient ℚ (tcPins D U gen) ψ (archCasimirAt hw φ) α := by
  have hHH := tc_archDerivAt_coefficient hw D U gen ψ hψ (hsm.archDerivAt .H) (isKfSmooth_archDerivAt hw hKf .H)
    α .H
  have hH := tc_archDerivAt_coefficient hw D U gen ψ hψ hsm hKf α .H
  have hFm := tc_archDerivAt_coefficient hw D U gen ψ hψ hsm hKf α .Fm
  have hEFm := tc_archDerivAt_coefficient hw D U gen ψ hψ (hsm.archDerivAt .Fm) (isKfSmooth_archDerivAt hw hKf .Fm)
    α .E
  have iHH := tc_integrable_integrand hw D U gen ψ hψ ((hsm.archDerivAt .H).archDerivAt .H)
    (isKfSmooth_archDerivAt hw (isKfSmooth_archDerivAt hw hKf .H) .H) α
  have iH := tc_integrable_integrand hw D U gen ψ hψ (hsm.archDerivAt .H) (isKfSmooth_archDerivAt hw hKf .H) α
  have iEFm := tc_integrable_integrand hw D U gen ψ hψ ((hsm.archDerivAt .Fm).archDerivAt .E)
    (isKfSmooth_archDerivAt hw (isKfSmooth_archDerivAt hw hKf .Fm) .E) α
  simp only [archCasimirAt]
  rw [hH, hHH, hFm, hEFm]
  funext g
  simp only [whittakerCoefficient, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
    add_mul, sub_mul, mul_assoc]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_add, MeasureTheory.integral_sub,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  all_goals first
    | exact iEFm g
    | exact ((iHH g).const_mul _).sub ((iH g).const_mul _)
    | exact (iHH g).const_mul _
    | exact (iH g).const_mul _

end Assembly

section Head

open IsDedekindDomain NumberField.AdelicBox

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ) (α : ℚ) :
    IsArchSmoothAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α) ∧
      (∀ d : ArchDir,
        archDerivAt hw d (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
          = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) α) ∧
      archCasimirAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
        = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archCasimirAt hw φ) α :=
  ⟨tc_isArchSmoothAt_coefficient hw D U gen ψ hψ hsm hKf α,
    fun d => tc_archDerivAt_coefficient hw D U gen ψ hψ hsm hKf α d,
    tc_archCasimirAt_coefficient hw D U gen ψ hψ hsm hKf α⟩

end Head

end

end S_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
end P2MW
export P2MW.S_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm (solution)
