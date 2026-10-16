-- Prove2me | solution 1 for OAI.ShortEgyptian.density_precise_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:49:42.973981+00:00
-- url     : https://prove2.me/submissions/060cf643-5274-4361-915f-0141296a6bd8

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentRecurrence.lean:L106-L143
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.density_precise_recurrence. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Theorems.Thm_OAI_ShortEgyptian_holder_density
import Theorems.Thm_OAI_ShortEgyptian_levelBad_residue
import Theorems.Thm_OAI_ShortEgyptian_level_fraction_lt
import Theorems.Thm_OAI_ShortEgyptian_residue_double_count

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem unitSum_scale (g : ℕ) (ns : List ℕ) :
    unitSum (ns.map (g * ·)) = unitSum ns / (g : ℚ) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, unitSum_cons, ih, Nat.cast_mul]
    rw [add_div]
    congr 1
    simp [div_eq_mul_inv, mul_comm]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma scaleRho_pos (S : ℝ) : 0 < scaleRho S := Real.exp_pos _
lemma scaleRho_le_one (S : ℝ) : scaleRho S ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have hh : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _; nlinarith)

lemma level_succ (S : ℝ) (j : ℕ) : level S (j+1) = level S j*scaleRho S := by
  unfold level scaleRho
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring

lemma level_antitone (S : ℝ) : Antitone (level S) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [level_succ]
  exact mul_le_of_le_one_right (level_pos S j).le (scaleRho_le_one S)

lemma level_before_depth (S : ℝ) (hm : 0 < scaleM S) (j : ℕ) :
    j < depth S ↔ Real.exp (scaleM S:ℝ) < level S j := by
  have hmR : 0 < (scaleM S:ℝ) := by exact_mod_cast hm
  rw [depth,Nat.lt_ceil,lt_div_iff₀ (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)]
  unfold level
  rw [Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

lemma levelMultiplier_pos (S : ℝ) (C j : ℕ) (hC : 0 < C) : 0 < levelMultiplier S C j := by
  unfold levelMultiplier
  split <;> omega

lemma levelMultiplier_dvd (S : ℝ) (C j : ℕ) :
    levelMultiplier S C (j+1) ∣ levelMultiplier S C j := by
  unfold levelMultiplier
  split_ifs with h₁ h₂ h₂
  · exact dvd_refl _
  · exact False.elim (h₂ (h₁.trans_le (level_antitone S (by omega))))
  · exact one_dvd _
  · exact dvd_refl _

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
lemma ListScale.m_pos {S : ℝ} (h : ListScale S) : 0 < scaleM S := by
  have hh : 0 < (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
  exact_mod_cast hh
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DescentSets ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma HasUnitSum.mono {M Q u k l : ℕ} (h : HasUnitSum M Q u k) (hkl : k ≤ l) : HasUnitSum M Q u l := by
  obtain ⟨ns,hs,hl⟩ := h
  exact ⟨ns,hs,hl.trans hkl⟩

lemma HasUnitSum.scale {M Q Q' u k : ℕ} (h : HasUnitSum M Q' u k)
    (hM : 0 < M) (hQ : 0 < Q) (hQ' : 0 < Q') (hd : Q' ∣ Q) : HasUnitSum M Q u k := by
  obtain ⟨ns,hs,hl⟩ := h
  let g := Q/Q'
  have hg : 0 < g := Nat.div_pos (Nat.le_of_dvd hQ hd) hQ'
  have heq : (g:ℚ)*Q'=Q := by exact_mod_cast Nat.div_mul_cancel hd
  refine ⟨ns.map (g*·),⟨?_,?_⟩,by simpa using hl⟩
  · intro n hn
    obtain ⟨n',hn',he⟩ := List.mem_map.mp hn
    subst n
    exact (hs.1 n' hn').trans (Nat.le_mul_of_pos_left _ hg)
  · rw [unitSum_scale,hs.2]
    have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hQq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hQ'q : (Q':ℚ) ≠ 0 := by exact_mod_cast hQ'.ne'
    have hgq : (g:ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp
    nlinarith

lemma mem_levelBad (S : ℝ) (M C K j u : ℕ) :
    u ∈ levelBad S M C K j ↔ 0 < u ∧ (u:ℝ) ≤ level S j ∧
      ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j)) := by
  constructor
  · intro hu
    obtain ⟨hu,hn⟩ := mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
    exact ⟨by omega,(Nat.cast_le.mpr hhi).trans (Nat.floor_le (level_pos S j).le),hn⟩
  · rintro ⟨hu0,hu,hn⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0,Nat.le_floor hu⟩,hn⟩

lemma levelBad_inherit (S : ℝ) (C M K j u : ℕ) (hM : 0 < M) (hC : 0 < C)
    (hu : u ∈ levelBad S M C K j) (hy : (u:ℝ) ≤ level S (j+1)) :
    u ∈ levelBad S M C K (j+1) := by
  obtain ⟨hu0,_,hn⟩ := (mem_levelBad S M C K j u).mp hu
  apply (mem_levelBad S M C K (j+1) u).mpr
  refine ⟨hu0,hy,?_⟩
  intro hh
  apply hn
  exact (hh.scale hM (levelMultiplier_pos S C j hC) (levelMultiplier_pos S C (j+1) hC)
    (levelMultiplier_dvd S C j)).mono (by omega)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentRecurrence ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter

lemma descentR_ge_two : 2 ≤ descentR := by norm_num [descentR]
lemma level_moment (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hC : 0 < C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S)
    (i : Fin (scaleM S) → Bool) :
    ∑ n ∈ Ioc (levelMultiplier S C j*R.t j i) (levelMultiplier S C j*R.t j i+⌊level S (j+1)⌋₊),
      (truncatedDivisorCount (level S j) n:ℝ)^descentR ≤ level S (j+1)*Real.exp (S^(1/4:ℝ)) := by
  let v := (dimX:ℝ)*S-(1/10000:ℝ)*scaleM S*j
  have hv : (scaleM S:ℝ) < v := Real.exp_lt_exp.mp ((level_before_depth S h.m_pos j).mp hj)
  have hvup : v ≤ (dimX:ℝ)*S := by
    dsimp [v]
    exact sub_le_self _ (by positivity)
  have hD : (dimX:ℝ) ≤ momentDimension := by norm_num [momentDimension,dimC,dimX,dimM]
  have hYlo : Real.exp (v/2) ≤ level S (j+1) := by
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [v] at hv ⊢
    nlinarith [show (0:ℝ) ≤ scaleM S by positivity]
  have hMpos : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  have htt : (R.t j i:ℝ) ≤ R.M := by exact_mod_cast Nat.le_of_dvd hMpos (R.t_dvd j i)
  have hcj : (levelMultiplier S C j:ℝ) ≤ C := by
    unfold levelMultiplier
    split
    · exact le_rfl
    · exact_mod_cast hC
  have hn : ((levelMultiplier S C j*R.t j i:ℕ):ℝ) ≤ Real.exp ((momentDimension:ℝ)*S) := by
    push_cast
    calc
      _ ≤ (C:ℝ)*R.M := mul_le_mul hcj htt (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ Real.exp (2*(dimC:ℝ)*S)*Real.exp ((dimM:ℝ)*S) := mul_le_mul hChi R.M_upper (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((2*(dimC:ℝ)+dimM)*S) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ h.S_pos.le
        norm_num [momentDimension,dimC,dimX,dimM]
  exact hm v (level S (j+1)) _ (h.m_bounds.1.trans hv.le)
    (hvup.trans (mul_le_mul_of_nonneg_right hD h.S_pos.le)) hYlo
    (level_antitone S (by omega)) hn

lemma shifted_subset_sum (H : Finset ℕ) (N : ℕ) (Y : ℝ) (f : ℕ → ℝ)
    (hH : ∀ u ∈ H, 0 < u ∧ (u:ℝ) ≤ Y) (hf : ∀ n, 0 ≤ f n) :
    ∑ u ∈ H, f (N+u) ≤ ∑ n ∈ Ioc N (N+⌊Y⌋₊), f n := by
  have hinj : Set.InjOn (N+·) (H: Set ℕ) := by intro a _ b _ hh; exact Nat.add_left_cancel hh
  rw [←sum_image hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hn
    have hh := hH u hu
    exact mem_Ioc.mpr ⟨by omega,Nat.add_le_add_left (Nat.le_floor hh.2) N⟩
  · exact fun n _ _ => hf n

lemma level_holder (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hC : 0 < C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S)
    (i : Fin (scaleM S) → Bool) :
    ∑ u ∈ levelBad S R.M C (terminalLength S) (j+1),
      (truncatedDivisorCount (level S j) (levelMultiplier S C j*R.t j i+u):ℝ) ≤
      level S (j+1)*Real.exp (S^(1/4:ℝ)/(descentR:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  apply holder_density _ _ descentR descentR_ge_two (by intros; positivity) _ _ (level_pos S (j+1))
  apply (shifted_subset_sum _ _ _ _ ?_ (by intros; positivity)).trans
    (level_moment S h hm C R hC hChi j hj i)
  intro u hu
  exact ((mem_levelBad S R.M C _ (j+1) u).mp hu).imp_right And.left

lemma density_precise_recurrence (S : ℝ) (h : ListScale S) (hm : MomentScale S) (C : ℕ) (R : ResidueSystem S C)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (j : ℕ) (hj : j < depth S) :
    levelDensity S R.M C j ≤ Real.exp (-(1/1000:ℝ)*scaleM S)+
      scaleRho S*levelDensity S R.M C (j+1)+
      2*Real.exp (S^(1/4:ℝ)/(descentR:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  have hC : 0 < C := by exact_mod_cast (Real.exp_pos _).trans_le hClo
  have hM : 0 < R.M := by exact_mod_cast (Real.exp_pos S).trans R.M_lower
  let H := levelBad S R.M C (terminalLength S) j
  let K := levelBad S R.M C (terminalLength S) (j+1)
  let N := fun i => levelMultiplier S C j*R.t j i
  have hH (u : ℕ) (hu : u ∈ H) : 0 < u ∧ (u:ℝ) ≤ level S j := by
    exact ((mem_levelBad S R.M C _ j u).mp hu).imp_right And.left
  have hI : 0 < (Fintype.card (Fin (scaleM S) → Bool):ℝ) := by exact_mod_cast Fintype.card_pos
  have hpair := residue_double_count H K (R.bad j) N
    (fun i => Nat.mul_pos (levelMultiplier_pos S C j hC) (R.t_pos j i)) _ _ _ (scaleRho_pos S) hH
    (fun u hu hy => levelBad_inherit S C R.M _ j u hM hC hu hy)
    (fun u hu i hy => levelBad_residue S C R.M _ j u (R.t j i) hM hC hj
      (level_fraction_lt S h C R.M j u R.M_lower hClo (hH u hu).2) hu (R.t_pos j i) (R.t_dvd j i) hy)
    (fun u hu hb hy => R.good_residues j hj u (by
      apply mem_Icc.mpr
      refine ⟨?_,Nat.le_floor (hH u hu).2⟩
      apply Nat.succ_le_iff.mpr
      apply (Nat.floor_lt (mul_nonneg (level_pos S j).le (scaleRho_pos S).le)).mpr
      simpa only [level_succ] using hy) hb)
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (scaleM S) → Bool))) =>
    level_holder S h hm C R hC hChi j hj i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  have hcoeff : 0 ≤ 2/(scaleRho S*Fintype.card (Fin (scaleM S) → Bool)) := div_nonneg (by norm_num) (mul_nonneg (scaleRho_pos S).le (Nat.cast_nonneg _))
  have hb := R.bad_card j hj
  have hh := hpair.trans (add_le_add (add_le_add hb (le_refl (K.card:ℝ)))
    (mul_le_mul_of_nonneg_left hsum hcoeff))
  apply (div_le_iff₀ (level_pos S j)).mpr
  change (H.card:ℝ) ≤ _
  apply hh.trans_eq
  dsimp [levelDensity,K,N]
  rw [level_succ]
  field_simp [(scaleRho_pos S).ne',(level_pos S j).ne',hI.ne']

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter


theorem solution : type_of% @_root_.OAI.ShortEgyptian.density_precise_recurrence := @_root_.OAI.ShortEgyptian.density_precise_recurrence
