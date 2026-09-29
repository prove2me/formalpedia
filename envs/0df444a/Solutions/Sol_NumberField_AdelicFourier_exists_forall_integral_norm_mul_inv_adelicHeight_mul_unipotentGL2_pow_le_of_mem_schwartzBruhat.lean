-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/93f3aed2-6010-57c8-b9b3-1ce246e1ca0b

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight
open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates

noncomputable section

namespace C5aD5

variable {F : Type} [Field F] [NumberField F]

theorem det_fst_apply (X : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archComponent F w (glArch (𝓞 F) F X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval F w).comp (adeleArch (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

theorem det_snd_apply (X : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

theorem fst_apply_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) : (a : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  change (a : AdeleRing (𝓞 F) F).1 w * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 at this
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem snd_apply_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : (a : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h0
  have := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) a.mul_inv
  change (a : AdeleRing (𝓞 F) F).2 v * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 at this
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem continuous_entry_fst (i j : Fin 2) (w : InfinitePlace F) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w :=
  (continuous_apply w).comp (continuous_fst.comp ((Units.continuous_val.matrix_elem i j)))

theorem rowNormSq_mul_unipotent_le {K : Type*} [NormedField K] (g : GL (Fin 2) K) (x : K) {m : ℝ}
    (hc : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ m) (hd : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ m) :
    rowNormSq ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≤ 3 * m ^ 2 * (1 + ‖x‖ ^ 2) := by
  have hm : 0 ≤ m := (norm_nonneg _).trans hc
  have e10 : ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  have e11 : ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
      = (g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  rw [rowNormSq, e10, e11]
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ m * ‖x‖ + m :=
    (norm_add_le _ _).trans (add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hd)
  have h2 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have h3 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 ≤ (m * ‖x‖ + m) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x, sq_nonneg m]

theorem exists_archHeight_inv_le (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g ∈ C, ∀ x : AdeleRing (𝓞 F) F,
      (archHeight F (glArch (𝓞 F) F (g * unipotentGL2 x)))⁻¹
        ≤ K * ∏ w : InfinitePlace F, (1 + ‖x.1 w‖ ^ 2) ^ w.mult := by
  classical
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨0, le_rfl, fun g hg => by simp [hCe] at hg⟩

  set E : AdelicGL2 (𝓞 F) F → ℝ := fun g => ∑ w : InfinitePlace F,
    (‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w‖ + ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖)
    with hEdef
  have hEc : Continuous E := by
    refine continuous_finset_sum _ fun w _ => ?_
    exact ((continuous_entry_fst 1 0 w).norm).add ((continuous_entry_fst 1 1 w).norm)
  obtain ⟨gM, hgM, hM⟩ := hC.exists_isMaxOn hCne hEc.continuousOn
  set m : ℝ := E gM with hmdef
  have hm : ∀ g ∈ C, ∀ w : InfinitePlace F,
      ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w‖ ≤ m ∧
      ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ ≤ m := by
    intro g hg w
    have hle : E g ≤ m := hM hg
    have h1 := Finset.single_le_sum (f := fun w : InfinitePlace F =>
      ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w‖ + ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖)
      (fun w _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ w)
    have h2 : ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w‖ + ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖
        ≤ m := h1.trans hle
    exact ⟨le_of_add_le_of_nonneg_left h2 (norm_nonneg _), le_of_add_le_of_nonneg_right h2 (norm_nonneg _)⟩

  set D : AdelicGL2 (𝓞 F) F → ℝ := fun g => ∑ w : InfinitePlace F,
    ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖⁻¹ with hDdef
  have hdetc : ∀ w : InfinitePlace F, Continuous fun g : AdelicGL2 (𝓞 F) F =>
      ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ := by
    intro w
    have : Continuous fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det) :=
      Units.continuous_val.matrix_det
    exact ((continuous_apply w).comp (continuous_fst.comp this)).norm
  have hDc : Continuous D := by
    refine continuous_finset_sum _ fun w _ => ?_
    exact (hdetc w).inv₀ fun g => norm_ne_zero_iff.mpr (fst_apply_ne_zero _ w)
  obtain ⟨gD, hgD, hDM⟩ := hC.exists_isMaxOn hCne hDc.continuousOn
  set Dm : ℝ := D gD with hDmdef
  have hDm : ∀ g ∈ C, ∀ w : InfinitePlace F,
      ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖⁻¹ ≤ Dm := by
    intro g hg w
    have hle : D g ≤ Dm := hDM hg
    exact (Finset.single_le_sum (f := fun w : InfinitePlace F =>
      ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖⁻¹)
      (fun w _ => inv_nonneg.mpr (norm_nonneg _)) (Finset.mem_univ w)).trans hle
  have hm0 : 0 ≤ m := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact (norm_nonneg _).trans (hm gM hgM w).1
  have hDm0 : 0 ≤ Dm := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact (inv_nonneg.mpr (norm_nonneg _)).trans (hDm gM hgM w)
  clear_value m Dm
  clear hDmdef hmdef hDM hgD gD hDc hdetc hDdef D hM hgM hEc hEdef E
  refine ⟨∏ w : InfinitePlace F, (3 * m ^ 2 * Dm) ^ w.mult, Finset.prod_nonneg fun w _ => by positivity, fun g hg x => ?_⟩

  have hloc : ∀ w : InfinitePlace F,
      (localHeight (archComponent F w (glArch (𝓞 F) F (g * unipotentGL2 x))))⁻¹ ≤ 3 * m ^ 2 * Dm * (1 + ‖x.1 w‖ ^ 2) := by
    intro w
    have hcomp : archComponent F w (glArch (𝓞 F) F (unipotentGL2 x)) = unipotentGL2 (x.1 w) := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [map_mul, map_mul, hcomp, localHeight, inv_div]
    have hrow := rowNormSq_mul_unipotent_le (archComponent F w (glArch (𝓞 F) F g)) (x.1 w) (hm g hg w).1 (hm g hg w).2
    have hdet : ‖((archComponent F w (glArch (𝓞 F) F g) * unipotentGL2 (x.1 w) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖
        = ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ := by
      rw [det_fst_apply, Units.val_mul, Matrix.det_mul]
      simp [unipotentGL2, Matrix.det_fin_two_of]
    rw [hdet, div_eq_mul_inv]
    have hdpos : 0 < ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ :=
      norm_pos_iff.mpr (fst_apply_ne_zero _ w)
    calc rowNormSq ((archComponent F w (glArch (𝓞 F) F g) * unipotentGL2 (x.1 w) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion)
          * ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖⁻¹
        ≤ (3 * m ^ 2 * (1 + ‖x.1 w‖ ^ 2)) * Dm :=
          mul_le_mul hrow (hDm g hg w) (inv_nonneg.mpr hdpos.le) (by positivity)
      _ = 3 * m ^ 2 * Dm * (1 + ‖x.1 w‖ ^ 2) := by ring

  unfold archHeight
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => inv_nonneg.mpr (pow_nonneg (localHeight_pos _).le _)) fun w _ => ?_
  rw [← mul_pow, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (localHeight_pos _).le) (hloc w) _

end C5aD5

namespace C5aD5

variable {F : Type} [Field F] [NumberField F]

theorem continuous_entry_snd (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 :=
  continuous_snd.comp (Units.continuous_val.matrix_elem i j)

theorem hasFiniteMulSupport_max_one_norm_sq (z : FiniteAdeleRing (𝓞 F) F) :
    (fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖z v‖ ^ 2).HasFiniteMulSupport := by
  refine Filter.eventually_cofinite.mp ?_
  filter_upwards [z.2] with v hv
  have h1 : ‖z v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  rw [max_eq_left h1, one_pow]

theorem rowMaxNorm_mul_unipotent_le {K : Type*} [NormedField K] [IsUltrametricDist K] (g : GL (Fin 2) K) (x : K) {m : ℝ}
    (hc : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ m) (hd : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ m) :
    rowMaxNorm ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≤ m * max 1 ‖x‖ := by
  have hm : 0 ≤ m := (norm_nonneg _).trans hc
  have e10 : ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  have e11 : ((g * unipotentGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
      = (g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2]
  rw [rowMaxNorm, e10, e11]
  refine max_le ?_ ?_
  · exact hc.trans (le_mul_of_one_le_right hm (le_max_left _ _))
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul hc (le_max_right _ _) (norm_nonneg _) hm
    · exact hd.trans (le_mul_of_one_le_right hm (le_max_left _ _))

theorem exists_finHeight_inv_le (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ A : HeightOneSpectrum (𝓞 F) → ℝ, (∀ v, 0 ≤ A v) ∧ A.HasFiniteMulSupport ∧ ∀ g ∈ C, ∀ x : AdeleRing (𝓞 F) F,
      (finHeight F (glFin (𝓞 F) F (g * unipotentGL2 x)))⁻¹
        ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), A v * max 1 ‖x.2 v‖ ^ 2 := by
  classical

  set E : Set (FiniteAdeleRing (𝓞 F) F) :=
    ((fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) '' C)
      ∪ ((fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) '' C) with hEdef
  have hE : IsCompact E := (hC.image (continuous_entry_snd 1 0)).union (hC.image (continuous_entry_snd 1 1))
  obtain ⟨s, hs0, hs⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hE

  set Dset : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun g : AdelicGL2 (𝓞 F) F => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) '' C
    with hDsetdef
  have hdetcont : Continuous fun g : AdelicGL2 (𝓞 F) F => (Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) := by
    refine Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, ?_⟩
    have : (fun g : AdelicGL2 (𝓞 F) F => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = fun g => ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det
  have hDset : IsCompact Dset := hC.image (continuous_snd.comp (Units.continuous_coe_inv.comp hdetcont))
  obtain ⟨s', hs'0, hs'⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hDset

  set ns : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖FinitePlace.embedding v ((s : 𝓞 F) : F)‖ with hnsdef
  set ns' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖FinitePlace.embedding v ((s' : 𝓞 F) : F)‖ with hns'def
  have hsF : ((s : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hs0
  have hs'F : ((s' : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hs'0
  have hns0 : ∀ v, 0 < ns v := fun v => norm_pos_iff.mpr ((map_ne_zero _).mpr hsF)
  have hns'0 : ∀ v, 0 < ns' v := fun v => norm_pos_iff.mpr ((map_ne_zero _).mpr hs'F)
  have hnsfin : ns.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hsF
  have hns'fin : ns'.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hs'F
  have le_inv_of_mul_le_one : ∀ {a b : ℝ}, 0 < a → a * b ≤ 1 → b ≤ a⁻¹ := by
    intro a b ha h
    calc b = a⁻¹ * (a * b) := by field_simp
      _ ≤ a⁻¹ * 1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
      _ = a⁻¹ := mul_one _

  have hent : ∀ g ∈ C, ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0‖ ≤ (ns v)⁻¹ ∧
      ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1‖ ≤ (ns v)⁻¹ := by
    intro g hg v
    have key : ∀ y ∈ E, ‖y v‖ ≤ (ns v)⁻¹ := by
      intro y hy
      have hint := norm_le_one_of_mem_adicCompletionIntegers (hs y hy v)
      have hint' : ns v * ‖y v‖ ≤ 1 := by
        convert hint using 1
        show ‖FinitePlace.embedding v ((s : 𝓞 F) : F)‖ * ‖y v‖ = _
        rw [← norm_mul]
        rfl
      exact le_inv_of_mul_le_one (hns0 v) hint'
    refine ⟨key _ (Set.mem_union_left _ ⟨g, hg, rfl⟩), key _ (Set.mem_union_right _ ⟨g, hg, rfl⟩)⟩

  have hdet : ∀ g ∈ C, ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖⁻¹
        ≤ (ns' v)⁻¹ := by
    intro g hg v
    have hint0 := norm_le_one_of_mem_adicCompletionIntegers (hs' _ ⟨g, hg, rfl⟩ v)
    have hint : ns' v * ‖(((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := by
      convert hint0 using 1
      show ‖FinitePlace.embedding v ((s' : 𝓞 F) : F)‖ * _ = _
      rw [← norm_mul]
      rfl
    have hinv : (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
        = (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)⁻¹ := by
      have hmul := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) (Matrix.GeneralLinearGroup.det g).mul_inv
      change ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v *
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 at hmul
      exact (eq_inv_of_mul_eq_one_right hmul)
    rw [hinv, norm_inv, det_snd_apply] at hint
    exact le_inv_of_mul_le_one (hns'0 v) hint

  refine ⟨fun v => (ns v)⁻¹ ^ 2 * (ns' v)⁻¹, fun v => by positivity, ?_, fun g hg x => ?_⟩
  · refine ((hnsfin.inv.pow 2).mul hns'fin.inv).subset ?_
    exact subset_rfl

  have hcomp : ∀ v : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F v (glFin (𝓞 F) F (unipotentGL2 x)) = unipotentGL2 (x.2 v) := by
    intro v
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (g * unipotentGL2 x))))⁻¹
        ≤ (ns v)⁻¹ ^ 2 * (ns' v)⁻¹ * max 1 ‖x.2 v‖ ^ 2 := by
    intro v
    rw [map_mul, map_mul, hcomp, finLocalHeight, inv_div]
    have hrow := rowMaxNorm_mul_unipotent_le (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) (x.2 v) (hent g hg v).1 (hent g hg v).2
    have hdet' : ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) * unipotentGL2 (x.2 v) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖
        = ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ := by
      rw [Units.val_mul, Matrix.det_mul]
      simp [unipotentGL2, Matrix.det_fin_two_of]
    rw [hdet', div_eq_mul_inv]
    have hr0 : 0 ≤ rowMaxNorm ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) * unipotentGL2 (x.2 v) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := rowMaxNorm_nonneg _
    calc rowMaxNorm ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) * unipotentGL2 (x.2 v) : GL (Fin 2) (v.adicCompletion F)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ^ 2
          * ‖((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖⁻¹
        ≤ ((ns v)⁻¹ * max 1 ‖x.2 v‖) ^ 2 * (ns' v)⁻¹ :=
          mul_le_mul (pow_le_pow_left₀ hr0 hrow 2) (hdet g hg v) (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      _ = (ns v)⁻¹ ^ 2 * (ns' v)⁻¹ * max 1 ‖x.2 v‖ ^ 2 := by ring

  unfold finHeight
  rw [← finprod_inv_distrib]
  refine finprod_le_finprod (hasFiniteMulSupport_finLocalHeight _).inv (fun v => inv_nonneg.mpr (finLocalHeight_pos _).le)
    ?_ hloc
  exact (((hnsfin.inv.pow 2).mul hns'fin.inv).mul (hasFiniteMulSupport_max_one_norm_sq x.2))

end C5aD5

namespace C5aD5

variable {F : Type} [Field F] [NumberField F]

section Weight

open scoped Classical

def archWeight (F : Type) [Field F] [NumberField F] (u : mixedEmbedding.mixedSpace F) : ℝ :=
  (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + ‖u.1 w‖ ^ 2)) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + ‖u.2 w‖ ^ 2) ^ 2

theorem one_le_archWeight (u : mixedEmbedding.mixedSpace F) : 1 ≤ archWeight F u := by
  unfold archWeight
  refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod fun w _ => ?_) (Finset.one_le_prod fun w _ => ?_)
  · nlinarith [sq_nonneg ‖u.1 w‖]
  · nlinarith [sq_nonneg ‖u.2 w‖]

theorem archWeight_pos (u : mixedEmbedding.mixedSpace F) : 0 < archWeight F u :=
  lt_of_lt_of_le one_pos (one_le_archWeight u)

theorem hasTemperateGrowth_archWeight_pow (M : ℕ) :
    Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => archWeight F u ^ M) := by

  have hre : ∀ w : {w : InfinitePlace F // w.IsReal},
      Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => 1 + ‖u.1 w‖ ^ 2) := by
    intro w
    have h1 : Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => u.1 w) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) w).comp
        (ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
          ({w : InfinitePlace F // w.IsComplex} → ℂ))).hasTemperateGrowth
    have h2 := (Function.HasTemperateGrowth.const (1 : ℝ)).add (h1.pow 2)
    convert h2 using 1
    funext u
    simp [Real.norm_eq_abs, sq_abs]
  have hco : ∀ w : {w : InfinitePlace F // w.IsComplex},
      Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => (1 + ‖u.2 w‖ ^ 2) ^ 2) := by
    intro w
    have hR : Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => (u.2 w).re) :=
      (Complex.reCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ) w).comp
        (ContinuousLinearMap.snd ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
          ({w : InfinitePlace F // w.IsComplex} → ℂ)))).hasTemperateGrowth
    have hI : Function.HasTemperateGrowth (fun u : mixedEmbedding.mixedSpace F => (u.2 w).im) :=
      (Complex.imCLM.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ) w).comp
        (ContinuousLinearMap.snd ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
          ({w : InfinitePlace F // w.IsComplex} → ℂ)))).hasTemperateGrowth
    have h2 := ((Function.HasTemperateGrowth.const (1 : ℝ)).add ((hR.pow 2).add (hI.pow 2))).pow 2
    convert h2 using 1 <;> try rfl
    funext u
    simp only [Pi.pow_apply, Pi.add_apply, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hprodR : Function.HasTemperateGrowth
      (fun u : mixedEmbedding.mixedSpace F => ∏ w : {w : InfinitePlace F // w.IsReal}, (1 + ‖u.1 w‖ ^ 2)) := by
    classical
    induction (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}) using Finset.induction_on with
    | empty => simpa using Function.HasTemperateGrowth.const (1 : ℝ)
    | insert w s hw ih =>
      have := (hre w).mul ih
      convert this using 1 <;> try rfl
      funext u
      rw [Finset.prod_insert hw]
      rfl
  have hprodC : Function.HasTemperateGrowth
      (fun u : mixedEmbedding.mixedSpace F => ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + ‖u.2 w‖ ^ 2) ^ 2) := by
    classical
    induction (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}) using Finset.induction_on with
    | empty => simpa using Function.HasTemperateGrowth.const (1 : ℝ)
    | insert w s hw ih =>
      have := (hco w).mul ih
      convert this using 1 <;> try rfl
      funext u
      rw [Finset.prod_insert hw]
      rfl
  have h := (hprodR.mul hprodC).pow M
  convert h using 1 <;> try rfl

end Weight

end C5aD5

namespace C5aD5

variable {F : Type} [Field F] [NumberField F]

section Link

open scoped Classical

theorem norm_ringEquiv_fst (y : InfiniteAdeleRing F) (w : InfinitePlace F) (hw : w.IsReal) :
    ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F y).1 ⟨w, hw⟩‖ = ‖y w‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _

theorem norm_ringEquiv_snd (y : InfiniteAdeleRing F) (w : InfinitePlace F) (hw : w.IsComplex) :
    ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F y).2 ⟨w, hw⟩‖ = ‖y w‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem prod_pow_mult_eq_archWeight (y : InfiniteAdeleRing F) :
    ∏ w : InfinitePlace F, (1 + ‖y w‖ ^ 2) ^ w.mult = archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F y) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun w : InfinitePlace F => w.IsReal), archWeight]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [norm_ringEquiv_fst y w.1 w.2, mult, if_pos w.2, pow_one]
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _ fun w => ?_
    have e : (Equiv.subtypeEquivRight (fun w : InfinitePlace F => (not_isReal_iff_isComplex (w := w)))) w
        = ⟨w.1, not_isReal_iff_isComplex.mp w.2⟩ := rfl
    rw [e, norm_ringEquiv_snd y w.1 (not_isReal_iff_isComplex.mp w.2), mult, if_neg w.2]

end Link

end C5aD5

namespace C5aD5

variable {F : Type} [Field F] [NumberField F]

section Main

open scoped Classical

theorem continuous_unipotentGL2 : Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

theorem continuous_gaugePow (g : AdelicGL2 (𝓞 F) F) (M : ℕ) :
    Continuous fun x : AdeleRing (𝓞 F) F => (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M := by
  have hc : Continuous fun x : AdeleRing (𝓞 F) F => adelicHeight F (g * unipotentGL2 x) :=
    (NumberField.AdelicHeight.continuous_adelicHeight F).comp (continuous_const.mul continuous_unipotentGL2)
  exact (hc.inv₀ fun x => (adelicHeight_pos _).ne').pow M

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F)
      = fun x => (fun v => Completion.extensionEmbeddingOfIsReal v.2 (x v.1), fun v => Completion.extensionEmbedding v.1 (x v.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem exists_gauge (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ A : HeightOneSpectrum (𝓞 F) → ℝ, (∀ v, 0 ≤ A v) ∧ A.HasFiniteMulSupport ∧
      ∀ g ∈ C, ∀ x : AdeleRing (𝓞 F) F,
        (adelicHeight F (g * unipotentGL2 x))⁻¹
          ≤ K * archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
              * ∏ᶠ v : HeightOneSpectrum (𝓞 F), A v * max 1 ‖x.2 v‖ ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := exists_archHeight_inv_le C hC
  obtain ⟨A, hA, hAfin, hAb⟩ := exists_finHeight_inv_le C hC
  refine ⟨K, hK, A, hA, hAfin, fun g hg x => ?_⟩
  rw [adelicHeight, mul_inv, ← prod_pow_mult_eq_archWeight]
  refine mul_le_mul (hKb g hg x) (hAb g hg x) (inv_nonneg.mpr (finHeight_pos _).le)
    (mul_nonneg hK (Finset.prod_nonneg fun w _ => by positivity))

theorem pureTensor_case
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (gS : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) (h : FiniteAdeleRing (𝓞 F) F → ℂ)
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (M : ℕ) :
    ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F =>
        ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I := by
  obtain ⟨K, hK, A, hA, hAfin, hgauge⟩ := exists_gauge C hC

  obtain ⟨sh, hsh0, hsh⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hcs
  set nh : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖FinitePlace.embedding v ((sh : 𝓞 F) : F)‖ with hnhdef
  have hshF : ((sh : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hsh0
  have hnh0 : ∀ v, 0 < nh v := fun v => norm_pos_iff.mpr ((map_ne_zero _).mpr hshF)
  have hnhfin : nh.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hshF
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => max 1 ((nh v)⁻¹ ^ 2) with hqdef
  have hqfin : q.HasFiniteMulSupport := by
    refine hnhfin.subset fun v hv => ?_
    intro h1
    apply hv
    simp only [hqdef, h1, inv_one, one_pow, max_self]
  set Pfin : ℝ := ∏ᶠ v, A v * q v with hPfindef
  have hPf : ∀ z ∈ tsupport h, ∏ᶠ v, A v * max 1 ‖z v‖ ^ 2 ≤ Pfin := by
    intro z hz
    refine finprod_le_finprod (hAfin.mul (hasFiniteMulSupport_max_one_norm_sq z)) (fun v => mul_nonneg (hA v) (by positivity))
      (hAfin.mul hqfin) fun v => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hA v)
    have hint := norm_le_one_of_mem_adicCompletionIntegers (hsh z hz v)
    have hint' : nh v * ‖z v‖ ≤ 1 := by
      convert hint using 1
      show ‖FinitePlace.embedding v ((sh : 𝓞 F) : F)‖ * ‖z v‖ = _
      rw [← norm_mul]
      rfl
    have hnv : nh v ≠ 0 := (hnh0 v).ne'
    have hzv : ‖z v‖ ≤ (nh v)⁻¹ := by
      calc ‖z v‖ = (nh v)⁻¹ * (nh v * ‖z v‖) := by rw [← mul_assoc, inv_mul_cancel₀ hnv, one_mul]
        _ ≤ (nh v)⁻¹ * 1 := mul_le_mul_of_nonneg_left hint' (inv_nonneg.mpr (hnh0 v).le)
        _ = (nh v)⁻¹ := mul_one _
    show max 1 ‖z v‖ ^ 2 ≤ max 1 ((nh v)⁻¹ ^ 2)
    rcases le_or_gt ‖z v‖ 1 with h1 | h1
    · rw [max_eq_left h1, one_pow]; exact le_max_left _ _
    · rw [max_eq_right h1.le]
      exact (pow_le_pow_left₀ (norm_nonneg _) hzv 2).trans (le_max_right _ _)
  have hPfin0 : 0 ≤ Pfin := finprod_nonneg fun v => mul_nonneg (hA v) (le_trans zero_le_one (le_max_left _ _))

  set G : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ :=
    SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun u => archWeight F u ^ M) gS with hGdef
  have hG : ∀ u, G u = (archWeight F u ^ M) • gS u := fun u => by
    rw [hGdef, SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_archWeight_pow M)]
  set hn : FiniteAdeleRing (𝓞 F) F → ℂ := fun z => (‖h z‖ : ℂ) with hhndef
  have hhn_lc : IsLocallyConstant hn := by
    rw [hhndef]
    exact hlc.comp (fun c : ℂ => ((‖c‖ : ℝ) : ℂ))
  have hhn_cs : HasCompactSupport hn := by
    rw [hhndef]
    exact hcs.comp_left (g := fun c : ℂ => ((‖c‖ : ℝ) : ℂ)) (by simp)
  set D : AdeleRing (𝓞 F) F → ℂ := fun x => G (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * hn x.2 with hDdef
  have hDmem : D ∈ NumberField.AdelicFourier.schwartzBruhat F :=
    Submodule.subset_span (NumberField.AdelicFourier.tensor_mem_pureTensorSet G hn hhn_lc hhn_cs)
  have hDint : Integrable D μ := NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F μ hDmem
  set c : ℝ := K ^ M * Pfin ^ M with hcdef
  have hc0 : 0 ≤ c := by positivity

  have hdom : ∀ g ∈ C, ∀ x : AdeleRing (𝓞 F) F,
      ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M
        ≤ c * ‖D x‖ := by
    intro g hg x
    by_cases hx : h x.2 = 0
    · rw [hx, mul_zero, norm_zero, zero_mul]; positivity
    have hxsupp : x.2 ∈ tsupport h := subset_tsupport _ (Function.mem_support.mpr hx)
    have hW := archWeight_pos (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
    have h1 : (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M
        ≤ (K * archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * Pfin) ^ M := by
      refine pow_le_pow_left₀ (inv_nonneg.mpr (adelicHeight_pos _).le) ((hgauge g hg x).trans ?_) M
      exact mul_le_mul_of_nonneg_left (hPf x.2 hxsupp) (mul_nonneg hK hW.le)
    have hDx : ‖D x‖ = archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) ^ M
        * ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)‖ * ‖h x.2‖ := by
      rw [hDdef]
      simp only [hG, hhndef, norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        abs_of_pos (pow_pos hW M)]
    rw [hDx, norm_mul]
    calc ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)‖ * ‖h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M
        ≤ ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)‖ * ‖h x.2‖
            * (K * archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * Pfin) ^ M :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c * (archWeight F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) ^ M
            * ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)‖ * ‖h x.2‖) := by
          rw [hcdef]; ring

  have hcontB : Continuous fun x : AdeleRing (𝓞 F) F => gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2 :=
    (gS.continuous.comp (continuous_ringEquiv_mixedSpace.comp continuous_fst)).mul (hlc.continuous.comp continuous_snd)
  refine ⟨c * ∫ x, ‖D x‖ ∂μ, fun g hg => ?_⟩
  have hmeas : AEStronglyMeasurable (fun x : AdeleRing (𝓞 F) F =>
      ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ :=
    (hcontB.norm.mul (continuous_gaugePow g M)).aestronglyMeasurable
  have hint : Integrable (fun x : AdeleRing (𝓞 F) F =>
      ‖gS (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ := by
    refine Integrable.mono' (hDint.norm.const_mul c) hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr (adelicHeight_pos _).le) _))]
    exact hdom g hg x
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint (hDint.norm.const_mul c) fun x => hdom g hg x

end Main

end C5aD5

end

open C5aD5 in
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (M : ℕ) :
    ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F => ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I := by

  suffices hP : Continuous B ∧ ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F => ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I from hP.2
  have hHm0 : ∀ (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F), 0 ≤ (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M :=
    fun g x => pow_nonneg (inv_nonneg.mpr (adelicHeight_pos _).le) _
  refine Submodule.span_induction (p := fun B _ => Continuous B ∧ ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F => ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I) ?_ ?_ ?_ ?_ hB
  ·
    rintro _ ⟨gS, h, hlc, hcs, rfl⟩
    refine ⟨(gS.continuous.comp (continuous_ringEquiv_mixedSpace.comp continuous_fst)).mul (hlc.continuous.comp continuous_snd), ?_⟩
    exact pureTensor_case μ gS h hlc hcs C hC M
  ·
    refine ⟨continuous_const, 0, fun g _ => ?_⟩
    simp
  ·
    rintro B₁ B₂ - - ⟨hc₁, I₁, h₁⟩ ⟨hc₂, I₂, h₂⟩
    refine ⟨hc₁.add hc₂, I₁ + I₂, fun g hg => ?_⟩
    obtain ⟨hi₁, hI₁⟩ := h₁ g hg
    obtain ⟨hi₂, hI₂⟩ := h₂ g hg
    have hle : ∀ x, ‖(B₁ + B₂) x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M
        ≤ ‖B₁ x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M + ‖B₂ x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M := by
      intro x
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hHm0 g x)
    have hmeas : AEStronglyMeasurable (fun x => ‖(B₁ + B₂) x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ :=
      ((hc₁.add hc₂).norm.mul (continuous_gaugePow g M)).aestronglyMeasurable
    have hint : Integrable (fun x => ‖(B₁ + B₂) x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ := by
      refine Integrable.mono' (hi₁.add hi₂) hmeas (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hHm0 g x))]
      exact hle x
    refine ⟨hint, ?_⟩
    calc ∫ x, ‖(B₁ + B₂) x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ
        ≤ ∫ x, (‖B₁ x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M + ‖B₂ x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) ∂μ :=
          integral_mono hint (hi₁.add hi₂) hle
      _ = _ := integral_add hi₁ hi₂
      _ ≤ I₁ + I₂ := add_le_add hI₁ hI₂
  ·
    rintro a B - ⟨hc, I, h⟩
    refine ⟨(hc.const_smul a : Continuous fun x => a • B x), ‖a‖ * I, fun g hg => ?_⟩
    obtain ⟨hi, hI⟩ := h g hg
    have he : (fun x => ‖(a • B) x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M)
        = fun x => ‖a‖ * (‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) := by
      funext x
      rw [Pi.smul_apply, norm_smul, mul_assoc]
    rw [he]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hI (norm_nonneg _)

end S_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat (solution)
