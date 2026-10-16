-- Prove2me | solution 1 for OAI.ShortEgyptian.assemble_residueSystem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:29:30.86526+00:00
-- url     : https://prove2.me/submissions/9a0bf0a6-fb20-4f28-94ee-e150beda4d06

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean:L52-L139
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.assemble_residueSystem. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_auxiliary_lower
import Theorems.Thm_OAI_ShortEgyptian_auxiliary_upper
import Theorems.Thm_OAI_ShortEgyptian_high_badLevel
import Theorems.Thm_OAI_ShortEgyptian_residue_list_discrepancy
import Theorems.Thm_OAI_ShortEgyptian_sample_dvd_auxiliary
import Theorems.Thm_OAI_ShortEgyptian_terminal_interval

-- ---- from OAI.NumberTheory.ShortEgyptian.ListSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma fourier_good_residues {I : Type uI} [Fintype I] [Nonempty I]
    (t : I → ℕ) (Q u : ℕ) (hQ : 0 < Q) (hu : 0 < u) (ht : ∀ i, 0 < t i)
    (δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/256) (hgood : ¬FourierBad t Q u δ) :
    δ*Fintype.card I/2 ≤
      ((univ.filter fun i => (residue (Q*t i) u (quotient (Q*t i) u):ℝ) < δ*u).card:ℝ) := by
  apply residue_list_discrepancy t Q u hQ hu ht δ hδ hsmall
  intro l hl hlH
  exact le_of_not_gt (fun h => hgood ⟨l,mem_Icc.mpr ⟨hl,hlH⟩,h⟩)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.LevelSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uD

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma scaleInterval_mem {X δ : ℝ} (hX : 0 ≤ X) {u : ℕ} (hu : u ∈ scaleInterval X δ) :
    0 < u ∧ X*δ < (u:ℝ) ∧ (u:ℝ) ≤ X := by
  obtain ⟨hl,hh⟩ := mem_Icc.mp hu
  refine ⟨by omega,?_,?_⟩
  · exact Nat.lt_of_floor_lt (by omega)
  · exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hX)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ListConstruction ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma deterministicProduct_pos {J : Type uJ} [Fintype J] (p : J → ℕ)
    (hp : ∀ j, 0 < p j) (I : J → Bool) : 0 < deterministicProduct p I := by
  apply prod_pos
  intro j _
  split <;> simp_all

lemma two_pow_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) :
    2^a ∣ auxiliaryDenominator a p₀ p f := by
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

lemma deterministic_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) (I : J → Bool) :
    deterministicProduct p₀ I ∣ auxiliaryDenominator a p₀ p f := by
  have hd : deterministicProduct p₀ I ∣ ∏ j,p₀ j := by
    apply prod_dvd_prod_of_dvd
    intro j _
    split <;> simp
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

lemma sampleProduct_pos {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (hp : ∀ a, 0 < p a) (f : (J × Bool) → A) (I : J → Bool) :
    0 < sampleProduct p I f := prod_pos (fun _ _ => hp _)

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

lemma level_zero (S : ℝ) : level S 0 = Real.exp ((dimX:ℝ)*S) := by simp [level]

lemma levelMultiplier_pos (S : ℝ) (C j : ℕ) (hC : 0 < C) : 0 < levelMultiplier S C j := by
  unfold levelMultiplier
  split <;> omega

lemma binary_power_upper (S : ℝ) (hlog : 1 ≤ Real.log S)
    (hS : 100001*Real.log S ≤ S) : (2:ℝ)^binaryExponent S ≤ Real.exp S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ 100000*Real.log S) hl2.le)
  have hh' := mul_lt_mul_of_pos_right hh hl2
  rw [add_mul,div_mul_cancel₀ _ hl2.ne',one_mul] at hh'
  have hl2hi : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); norm_num at hh ⊢; exact hh
  have he : (2:ℝ)^binaryExponent S = Real.exp ((binaryExponent S:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [he]
  exact Real.exp_le_exp.mpr (by dsimp [binaryExponent]; nlinarith)

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
lemma ListScale.m_hundred {S : ℝ} (h : ListScale S) : 100 ≤ (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
lemma exp_neg_small (v : ℝ) (hv : 2560000 ≤ v) : Real.exp (-(1/10000:ℝ)*v) ≤ 1/256 := by
  have hlog : Real.log 256 ≤ 255 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<256)
    norm_num at hh
    exact hh
  apply (Real.le_log_iff_exp_le (by norm_num : (0:ℝ)<1/256)).mp
  rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  linarith
lemma ListScale.rho_small {S : ℝ} (h : ListScale S) : scaleRho S ≤ 1/256 :=
  exp_neg_small _ (by linarith [h.m_large,h.log_large])
lemma ListScale.terminal_small {S : ℝ} (h : ListScale S) (u : ℕ)
    (hu : 100000*Real.log S ≤ Real.log u) : Real.exp (-(1/10000:ℝ)*Real.log u) ≤ 1/256 :=
  exp_neg_small _ (by linarith [h.log_large])

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uA

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma assemble_residueSystem {A : Type uA} (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (p₀ : Fin (scaleM S) → ℕ) (hp₀ : ∀ j, (p₀ j).Prime) (hinj : Function.Injective p₀)
    (hp₀max : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp₀min : ∀ j, S^100 ≤ (p₀ j:ℝ))
    (p : A → ℕ) (hp : ∀ x, (p x).Prime) (hpmax : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (f : Fin 1000 → (Fin (scaleM S) × Bool) → A)
    (hf : ∀ j, j < depth S → level S j ≤ Real.exp S →
      ((badLevel (fun I => sampleProduct p I (f 0)) 1 (level S j) (scaleRho S)).card:ℝ) ≤
        level S j*Real.exp (-(1/1000:ℝ)*scaleM S))
    (hterm : ∀ u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊,
      ∃ i, ¬FourierBad (fun I => sampleProduct p I (f i)) 1 u
        (Real.exp (-(1/10000:ℝ)*Real.log u))) :
    Nonempty (ResidueSystem S C) := by
  let M := auxiliaryDenominator (binaryExponent S) p₀ p f
  have hp₀pos (j : Fin (scaleM S)) : 0 < p₀ j := (hp₀ j).pos
  have hppos (x : A) : 0 < p x := (hp x).pos
  have hmcard : (Fintype.card (Fin (scaleM S)):ℝ) ≤ S/Real.log S := by
    simpa only [Fintype.card_fin] using h.m_bounds.2.1
  have hMlo : Real.exp S < (M:ℝ) := auxiliary_lower S _ p₀ p f h.S_pos (by linarith [h.log_one])
    (by simpa only [Fintype.card_fin] using h.m_bounds.1) hp₀min hp₀pos hppos
  have hMhi : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S) := auxiliary_upper S _ p₀ p f h.two_le
    (by linarith [h.log_one]) hmcard hp₀max hpmax
    (binary_power_upper S h.log_one h.log_bound)
  let t (j : ℕ) : (Fin (scaleM S) → Bool) → ℕ :=
    if Real.exp S < level S j then deterministicProduct p₀ else fun I => sampleProduct p I (f 0)
  have htpos (j : ℕ) (I : Fin (scaleM S) → Bool) : 0 < t j I := by
    dsimp [t]
    split
    · exact deterministicProduct_pos p₀ hp₀pos I
    · exact sampleProduct_pos p hppos (f 0) I
  have htdvd (j : ℕ) (I : Fin (scaleM S) → Bool) : t j I ∣ M := by
    dsimp [t]
    split
    · exact deterministic_dvd_auxiliary _ p₀ p f I
    · exact sample_dvd_auxiliary _ p₀ p f 0 I
  let B (j : ℕ) := badLevel (t j) (levelMultiplier S C j) (level S j) (scaleRho S)
  have hB (j : ℕ) (hj : j < depth S) : ((B j).card:ℝ) ≤ level S j*Real.exp (-(1/1000:ℝ)*scaleM S) := by
    by_cases hx : Real.exp S < level S j
    · dsimp only [B,t,levelMultiplier]
      simp only [ite_eq_left hx]
      exact high_badLevel S (level S j) C p₀ hp₀ hinj (Fintype.card_fin _)
        hp₀max h.two_le h.log_one h.m_hundred h.reciprocal_power
        h.reciprocal_const hx.le (by simpa only [level_zero] using level_antitone S (Nat.zero_le j)) hClo hChi
    · simpa only [B,t,levelMultiplier,ite_eq_right hx] using hf j hj (le_of_not_gt hx)
  have hC : 0 < C := by
    have hh : (0:ℝ)<C := (Real.exp_pos _).trans_le hClo
    exact_mod_cast hh
  refine ⟨⟨M,hMlo,hMhi,two_pow_dvd_auxiliary _ p₀ p f,t,htpos,htdvd,B,hB,?_,?_⟩⟩
  · intro j _hj u hu hbad
    have hu' := scaleInterval_mem (level_pos S j).le hu
    have hgood : ¬FourierBad (t j) (levelMultiplier S C j) u (scaleRho S) := by
      intro hbad'
      exact hbad (mem_filter.mpr ⟨hu,hbad'⟩)
    have hc := fourier_good_residues (t j) (levelMultiplier S C j) u
      (levelMultiplier_pos S C j hC) hu'.1 (htpos j) (scaleRho S) (scaleRho_pos S) h.rho_small hgood
    apply hc.trans
    apply Nat.cast_le.mpr
    apply card_le_card
    intro I hI
    refine mem_filter.mpr ⟨mem_univ I,?_⟩
    have hh := (mem_filter.mp hI).2
    rw [level_succ]
    exact hh.le.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu'.2.2 (scaleRho_pos S).le)
  · intro u hu huhi
    have huU : u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊ := mem_Icc.mpr ⟨by have hh := (Nat.floor_lt (by positivity : 0 ≤ S^100000)).mpr hu; omega,
      Nat.le_floor huhi⟩
    obtain ⟨i,hi⟩ := hterm u huU
    have huinfo := terminal_interval S h u huU
    have hu0 : 0 < u := by omega
    have hδ := Real.exp_pos (-(1/10000:ℝ)*Real.log u)
    have hc := fourier_good_residues (fun I => sampleProduct p I (f i)) 1 u (by norm_num) hu0
      (sampleProduct_pos p hppos (f i)) _ hδ (h.terminal_small u huinfo.2.1) hi
    have hcardpos : 0 < (Fintype.card (Fin (scaleM S) → Bool):ℝ) := by exact_mod_cast Fintype.card_pos
    have hne : (univ.filter fun I => (residue (1*sampleProduct p I (f i)) u
        (quotient (1*sampleProduct p I (f i)) u):ℝ) < Real.exp (-(1/10000:ℝ)*Real.log u)*u).Nonempty := by
      apply card_pos.mp
      exact_mod_cast (div_pos (mul_pos hδ hcardpos) (by norm_num : (0:ℝ)<2)).trans_le hc
    obtain ⟨I,hI⟩ := hne
    refine ⟨sampleProduct p I (f i),sampleProduct_pos p hppos (f i) I,
      sample_dvd_auxiliary _ p₀ p f i I,?_⟩
    have hh := (mem_filter.mp hI).2
    simp only [one_mul] at hh
    apply hh.le.trans_eq
    have huR : 0 < (u:ℝ) := by exact_mod_cast hu0
    rw [Real.rpow_def_of_pos huR,←Real.exp_log huR,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution.{uA} : type_of% @_root_.OAI.ShortEgyptian.assemble_residueSystem.{uA} := @_root_.OAI.ShortEgyptian.assemble_residueSystem.{uA}
