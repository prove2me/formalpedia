-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:21:32.771794+00:00
-- url     : https://prove2.me/submissions/25597e89-4fd7-4afb-9182-d9eba49593c7

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_three_small_protocol
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_public_complete

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

lemma best_spec (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V) :
    best F hF shape X ∈ F ∧
      ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape (best F hF shape X)).card :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma chosen_mem (k : ℕ) : chosen F hF shape X k ∈ F :=
  (best_spec F hF shape _).1

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma retained_half (threshold : ℕ) (hthreshold : 0 < threshold) :
    X.card ≤ 2*(retained F hF shape X threshold hthreshold).card := by
  have hsub := Finset.card_le_card (remaining_subset F hF shape X
    (stopIndex F hF shape X threshold hthreshold))
  unfold retained
  split
  · rename_i h
    rw [Finset.card_sdiff_of_subset (remaining_subset F hF shape X _)]
    exact h
  · rename_i h
    omega

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

lemma peel_half (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    X.card≤2*(peelSet e F hF shape X k hk).card := by
  unfold peelSet
  split_ifs
  · exact retained_half F hF shape X k hk
  · omega

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_LargeTrainingCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

theorem large_clipped_part (X S Y : Finset A) (hSX : S⊆X)
    (hret : X.card≤4*S.card) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (J : ℕ)
    (h : ¬∀i,(clippedPart S F hF shape Y J i).card≤(S.card:ℝ)/25) :
    ∃a∈F,(X.card:ℝ)≤100*(X∩shape a).card := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  have hlarge := lt_of_not_ge hi
  cases i with
  | none =>
    simp only [clippedPart,Finset.card_empty,Nat.cast_zero] at hlarge
    have hn : (0:ℝ)≤(S.card:ℝ)/25 := by positivity
    exact False.elim (not_lt_of_ge hn hlarge)
  | some i =>
    refine ⟨chosen F hF shape Y i,chosen_mem F hF shape Y i,?_⟩
    have hsub : clippedPart S F hF shape Y J (some i)⊆X∩shape (chosen F hF shape Y i) := by
      intro a ha
      have hm := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨hSX hm.1,(Finset.mem_inter.mp hm.2).2⟩
    have hc : ((clippedPart S F hF shape Y J (some i)).card:ℝ)≤(X∩shape (chosen F hF shape Y i)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hr : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
    nlinarith only [hc,hr,hlarge]

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_MetadataScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open Filter
open scoped Topology

lemma sigma_exp_absorb (C σ : ℝ) (hC : 0≤C) (hσ : 225*C≤σ) (hσ0 : 0≤σ) :
    C*σ*Real.exp (13*σ/15)≤Real.exp σ := by
  have hp := Real.pow_div_factorial_le_exp (2*σ/15) (by positivity : (0:ℝ)≤2*σ/15) 2
  norm_num only [Nat.factorial,Finset.prod_range_succ,Nat.cast_ofNat] at hp
  have hc : C*σ≤Real.exp (2*σ/15) := by nlinarith
  calc
    _≤Real.exp (2*σ/15)*Real.exp (13*σ/15) := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _=Real.exp σ := by rw [←Real.exp_add];congr 1;ring

lemma metadata_budget (σ H J B V : ℝ) (hσ : 100000≤σ)
    (hH : 0≤H) (hJ : 0≤J) (_hB : 0<B) (_hV : 0<V)
    (hHhi : H≤5*Real.exp (σ/2)) (hJhi : J≤5*Real.exp (13*σ/15))
    (hHlog : Real.log (H+1)≤σ) (hBlog : Real.log B≤6*σ) (hVlog : Real.log V≤5*σ) :
    2*Real.log (H+1)+(10*H)*Real.log V+(1+2*H+J)*Real.log B≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have he : Real.exp (σ/2)≤Real.exp (13*σ/15) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1≤Real.exp (13*σ/15) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : H≤5*Real.exp (13*σ/15) := hHhi.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have h₁ := mul_le_mul_of_nonneg_left hVlog (by positivity : (0:ℝ)≤10*H)
  have h₂ := mul_le_mul_of_nonneg_left hBlog (by positivity : (0:ℝ)≤1+2*H+J)
  have h₃ := mul_le_mul_of_nonneg_left hh hσ0
  have h₄ := mul_le_mul_of_nonneg_left hJhi hσ0
  have h₅ := mul_le_mul_of_nonneg_left he1 hσ0
  apply le_trans _ (sigma_exp_absorb 400 σ (by norm_num) (by linarith) hσ0)
  nlinarith only [hHlog,h₁,h₂,h₃,h₄,h₅,mul_nonneg hσ0 (Real.exp_nonneg (13*σ/15))]

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetEncoding
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SubsetEncoding
open scoped Classical BigOperators

lemma log_factorial_lower (n : ℕ) :
    (n:ℝ)*Real.log n-n≤Real.log (n.factorial:ℝ) := by
  by_cases hn : n=0
  · subst n;norm_num
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Stirling.le_log_factorial_stirling hn
  have hp : (1:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hl := Real.log_nonneg hp
  have hl' := Real.log_nonneg hn1
  linarith

lemma log_choose_le (m n : ℕ) (hnm : n ≤ m) :
    Real.log (m.choose n:ℝ)≤(n:ℝ)*(Real.log ((m:ℝ)/n)+1) := by
  by_cases hn : n=0
  · subst n;simp
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmpos : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hn).trans_le hnm
  have hcp : (0:ℝ) < m.choose n := by exact_mod_cast Nat.choose_pos hnm
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.log_le_log hcp (Nat.choose_le_pow_div n m : (m.choose n:ℝ)≤(m:ℝ)^n/n.factorial)
  rw [Real.log_div (pow_ne_zero _ hmpos.ne') hfact.ne',Real.log_pow] at h
  rw [Real.log_div hmpos.ne' hnpos.ne']
  have hf := log_factorial_lower n
  nlinarith

variable {α : Type*} [Fintype α]

lemma alphabet_card (U : Finset α) (n : ℕ) :
    Fintype.card (Alphabet U n)=U.card.choose n := by
  classical
  unfold Alphabet
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun A : Finset α=>A⊆U ∧ A.card=n)=U.powersetCard n := by
    ext A;simp
  rw [he,Finset.card_powersetCard]

lemma decode_encode (S U : Finset α) (hSU : S⊆U) : decode U S.card (encode S U hSU)=S := by
  exact congrArg Subtype.val ((Fintype.equivFin (Alphabet U S.card)).symm_apply_apply ⟨S,hSU,rfl⟩)

theorem small_set_description (S U : Finset α) (hSU : S⊆U)
    (q P : ℝ) (hn : (S.card:ℝ)≤100*q*P) :
    decode U S.card (encode S U hSU)=S ∧
    Real.log (Fintype.card (Alphabet U S.card):ℝ)≤
      100*q*P*(Real.log ((U.card:ℝ)/S.card)+1) := by
  refine ⟨decode_encode S U hSU,?_⟩
  rw [alphabet_card]
  have h := log_choose_le U.card S.card (Finset.card_le_card hSU)
  apply h.trans
  apply mul_le_mul_of_nonneg_right hn
  by_cases hs : S.card=0
  · simp [hs]
  · have hp : (0:ℝ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hp).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
    linarith [Real.log_nonneg hr]

end SharpRamseyFive.SubsetEncoding

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseDecoded_small (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) (m : Fin (Fintype.card (Alphabet U n))) :
    baseDecoded U n P τ L₀ t (by simpa only [baseAlphabet,hn,ite_true] using m)=decode U n m := by
  simp [baseDecoded,hn]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseAlphabetCost
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_small_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=Fintype.card (Alphabet U n) := by
  calc
    _ = Fintype.card (Fin (Fintype.card (Alphabet U n))) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_true]))
    _ = _ := Fintype.card_fin _

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

lemma piLaw_prod (p : ∀i,Law (β i)) (f : ∀i,β i→ℝ) :
    (∑x,piLaw p x*(∏i,f i (x i)))=∏i,∑a,p i a*f i a := by
  simp only [piLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a=>p i a*f i a)).symm

lemma piLaw_eval_expectation (p : ∀i,Law (β i)) (i : ι) (f : β i→ℝ) :
    (∑x,piLaw p x*f (x i))=∑a,p i a*f a := by
  let g : ∀j,β j→ℝ := fun j a=>if h : j=i then f (h ▸ a) else 1
  have hx (x : ∀j,β j) : (∏j,g j (x j))=f (x i) := by
    have he : (fun j=>g j (x j))=Function.update (fun _=>1) i (f (x i)) := by
      funext j
      by_cases hj : j=i
      · subst j;simp [g]
      · simp [g,hj]
    rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hs : (fun j=>∑a,p j a*g j a)=Function.update (fun _=>1) i (∑a,p i a*f a) := by
    funext j
    by_cases hj : j=i
    · subst j;simp [g]
    · simp [g,hj,(p j).sum_one]
  have hh := piLaw_prod p g
  simp_rw [hx] at hh
  rw [hs,Finset.prod_update_of_mem (Finset.mem_univ i)] at hh
  simpa using hh

lemma piLaw_eval (p : ∀i,Law (β i)) (i : ι) : map (piLaw p) (fun x=>x i)=p i := by
  apply Law.ext
  funext a
  have hm := piLaw_eval_expectation p i (fun b=>if b=a then 1 else 0)
  simpa only [map,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hm
end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

lemma finiteImageLaw_positive (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α)
    (a : α) (ha : 0<finiteImageLaw μ f a) : ∃ω,f ω=a := by
  have hh : μ.real {ω | f ω=a}≠0 := ne_of_gt ha
  exact nonempty_of_measureReal_ne_zero hh

lemma finiteImageLaw_event (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (E : Finset α) :
    eventMass (finiteImageLaw μ f) E=μ.real {ω | f ω∈E} := by
  have hd : Set.PairwiseDisjoint (E:Set α) (fun a=>{ω | f ω=a}) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have he : (⋃a∈E,{ω | f ω=a})={ω | f ω∈E} := by ext ω;simp
  have hh := measureReal_biUnion_finset (μ:=μ) hd
    (fun _ _=>Set.Countable.measurableSet (Set.to_countable _))
  rw [he] at hh
  exact hh.symm

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_none (P : Ω→α→Prop) (ω : Ω) :
    chooseMessage P ω=none ↔ ¬∃a,P ω a := by
  unfold chooseMessage
  split <;> simp_all

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_sound (P : Ω→α→Prop) (ω : Ω) (a : α)
    (h : chooseMessage P ω=some a) : P ω a := by
  unfold chooseMessage at h
  split at h
  next hh => exact (Option.some.inj h) ▸ hh.choose_spec
  next hh => contradiction

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped BigOperators Classical

lemma card_TwoListCode {V : Type*} [Fintype V] (h p B : ℕ) :
    Nat.card (TwoListCode V h p B)=Nat.card V^(5*(h+p))*(B+1)^(1+h+p+h*p) := by
  simp only [TwoListCode,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  simp only [pow_mul,pow_add,pow_one]
  ring

lemma card_profile (H J : ℕ) : Nat.card (ListProfile H J)≤(H+1)^2 := by
  have h := Nat.card_le_card_of_injective (fun z : ListProfile H J=>z.val) Subtype.val_injective
  simpa only [ListProfile,Nat.card_prod,Nat.card_fin,pow_two] using h

theorem card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Nat.card (TrainingCode V H J B)≤
      (H+1)^2*Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
  change Nat.card ((r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B)≤_
  rw [Nat.card_sigma]
  have hV : 1≤Nat.card V := Nat.card_pos
  calc
    _ ≤ ∑ _r : ListProfile H J,Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
      apply Finset.sum_le_sum
      intro r _
      rw [card_TwoListCode]
      have hh : r.val.1.val≤H := Nat.le_of_lt_succ r.val.1.isLt
      have hp : r.val.2.val≤H := Nat.le_of_lt_succ r.val.2.isLt
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hV (by omega))
        (Nat.pow_le_pow_right (by omega : 1≤B+1) (by have := r.prop;omega))
    _ = Nat.card (ListProfile H J)*(Nat.card V^(10*H)*(B+1)^(1+2*H+J)) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ (card_profile H J)

theorem log_card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Real.log (Nat.card (TrainingCode V H J B))≤
      2*Real.log (H+1)+(10*(H:ℝ))*Real.log (Nat.card V)+
        (1+2*(H:ℝ)+J)*Real.log (B+1) := by
  have hV : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have hh : (0:ℝ)<H+1 := by positivity
  have hb : (0:ℝ)<B+1 := by positivity
  have hc := Real.log_le_log (show (0:ℝ)<Nat.card (TrainingCode V H J B) by exact_mod_cast Nat.card_pos (α:=TrainingCode V H J B))
    (show (Nat.card (TrainingCode V H J B):ℝ)≤(H+1)^2*(Nat.card V:ℝ)^(10*H)*(B+1)^(1+2*H+J) by
      exact_mod_cast card_TrainingCode (V:=V) H J B)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hc
  push_cast at hc
  exact hc

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped Classical

lemma ceil_five_exp (x : ℝ) (hx : 0≤x) : (⌈4*Real.exp x⌉₊:ℝ)≤5*Real.exp x := by
  have hh := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤4*Real.exp x)
  have he := Real.one_le_exp_iff.mpr hx
  linarith

theorem log_card_training_le {V : Type*} [Fintype V] [Nonempty V]
    (σ : ℝ) (hσ : 100000≤σ) (hV : (Nat.card V:ℝ)≤Real.exp (5*σ)) :
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have hH := ceil_five_exp (σ/2) (by positivity)
  have hJ := ceil_five_exp (13*σ/15) (by positivity)
  have hv : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have he : 6≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
  have hx : 2≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
  have he5 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : (listCap σ:ℝ)+1≤Real.exp σ := by
    have hpow : Real.exp (σ/2)*Real.exp (σ/2)=Real.exp σ := by rw [←Real.exp_add];congr 1;ring
    dsimp only [listCap]
    nlinarith
  have hb : (Nat.card V:ℝ)+1≤Real.exp (6*σ) := by
    have hm : Real.exp σ*Real.exp (5*σ)=Real.exp (6*σ) := by rw [←Real.exp_add];congr 1;ring
    nlinarith
  have hhlog : Real.log ((listCap σ:ℝ)+1)≤σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(listCap σ:ℝ)+1) hh
    rwa [Real.log_exp] at h
  have hblog : Real.log ((Nat.card V:ℝ)+1)≤6*σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(Nat.card V:ℝ)+1) hb
    rwa [Real.log_exp] at h
  have hvlog : Real.log (Nat.card V)≤5*σ := by
    have h := Real.log_le_log hv hV
    rwa [Real.log_exp] at h
  exact (log_card_TrainingCode (V:=V) (listCap σ) (productCap σ) (Nat.card V)).trans
    (metadata_budget σ (listCap σ) (productCap σ) (Nat.card V+1) (Nat.card V)
      hσ (by positivity) (by positivity) (by positivity) hv hH hJ hhlog hblog hvlog)

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlatAtlas

open Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma decode_flatCode (n : ℕ) (hn : finrank K V≤n) (A : Submodule K V) :
    Submodule.span K (Set.range (flatCode n hn A))=A :=
  (exists_spanning_code A n hn).choose_spec

lemma flatCode_injective (n : ℕ) (hn : finrank K V≤n) : Function.Injective (flatCode n hn (K:=K) (V:=V)) := by
  intro A B hab
  rw [←decode_flatCode n hn A,←decode_flatCode n hn B,hab]

theorem card_submodules_le [Finite K] (n : ℕ) (hn : finrank K V≤n) :
    Nat.card (Submodule K V)≤(Nat.card V)^n := by
  let : Finite V := Module.finite_of_finite K
  have hh := Nat.card_le_card_of_injective (flatCode n hn (K:=K) (V:=V)) (flatCode_injective n hn)
  simpa only [Nat.card_fun,Nat.card_fin] using hh

end SharpRamseyFive.FlatAtlas

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoredMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in

lemma projective_header_le (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)≤6*(Nat.card K:ℝ) := by
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hp : (Fintype.card (ℙ K V):ℝ)≤Nat.card V := by
    exact_mod_cast projective_card_le_vectors (Finset.univ : Finset (ℙ K V))
  have he : Real.exp (5*σ)+1≤Real.exp (6*σ) := by
    have h1 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by linarith)
    have h2 : 2≤Real.exp σ := (by linarith : (2:ℝ)≤σ+1).trans (Real.add_one_le_exp σ)
    have hx : Real.exp (6*σ)=Real.exp (5*σ)*Real.exp σ := by
      rw [←Real.exp_add];congr 1;ring
    rw [hx]
    nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1)
    (show (Fintype.card (ℙ K V)+1:ℝ)≤Real.exp (6*σ) by linarith)
  rw [Real.log_exp] at hl
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  linarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseCapturedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy
open MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseOutcome_none (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    baseOutcome S U P τ R L₀ t=none ↔
      ¬∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  simp only [baseOutcome,Option.map_eq_none_iff,chooseMessage_none]

omit [Finite K] [FiniteDimensional K V] in
lemma baseCaptureLaw_positive (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (W : Finset (ℙ K V)) (hW : 0<baseCaptureLaw S U P τ R L₀ (some W)) :
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  obtain ⟨t,ht⟩ := finiteImageLaw_positive (baseTapeMeasure U P τ R L₀)
    (baseOutcome S U P τ R L₀) (some W) hW
  dsimp only [baseOutcome] at ht
  obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp ht
  have hs := chooseMessage_sound _ t m hm
  simpa only [he] using hs

omit [Finite K] [FiniteDimensional K V] in
lemma baseCaptureLaw_failure (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (E : Set (BaseTape U P τ R)) (ε : ℝ)
    (hE : (baseTapeMeasure U P τ R L₀).real Eᶜ≤ε)
    (hs : ∀t∈E,∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) :
    baseCaptureLaw S U P τ R L₀ none≤ε := by
  apply (measureReal_mono (μ:=baseTapeMeasure U P τ R L₀)
    (show {t | baseOutcome S U P τ R L₀ t=none}⊆Eᶜ from ?_)).trans hE
  intro t ht he
  exact (baseOutcome_none S U P τ R L₀ t).mp ht (hs t he)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy SubsetEncoding MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem baseSmallLaw (S U : Finset (ℙ K V)) (hSU : S⊆U) (P τ : ℝ)
    (hP : 1≤P) (hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P) (R : ℕ) (L₀ : ℝ≥0) :
    baseCaptureLaw S U P τ R L₀ none≤0 ∧
    Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  refine ⟨?_,?_⟩
  · apply baseCaptureLaw_failure S U P τ R L₀ Set.univ 0 (by simp)
    intro t _
    let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let m : baseAlphabet U S.card P τ := by
      simpa only [baseAlphabet,hn,ite_true] using encode S U hSU
    refine ⟨m,?_⟩
    have hd := baseDecoded_small U S.card P τ L₀ (t n) hn (encode S U hSU)
    change (baseDecoded U S.card P τ L₀ (t n) m)⊆U ∧
      ((baseDecoded U S.card P τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧
      (9/10:ℝ)*S.card≤((baseDecoded U S.card P τ L₀ (t n) m∩S).card:ℝ)
    rw [hd,decode_encode S U hSU,Finset.inter_self]
    refine ⟨hSU,?_,?_⟩
    · exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by linarith))
    · nlinarith only [show (0:ℝ)≤S.card by positivity]
  · rw [baseAlphabet_small_card U S.card P τ hn]
    have hc := (small_set_description S U hSU (Nat.card K) P hn).2
    exact hc.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
end

open Module ProjectiveIncidence FiniteEntropy Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_coordinates (e : V≃ₗ[K]W) (x : ℙ K V) (f : ℙ K (Dual K V)) :
    Incident (projectiveEquiv e x) (projectiveEquiv e.symm.dualMap f) ↔ Incident x f := by
  induction x using Projectivization.ind with | h v hv =>
  induction f using Projectivization.ind with | h a ha =>
  change Incident (Projectivization.map e.toLinearMap e.injective (Projectivization.mk K v hv))
    (Projectivization.map e.symm.dualMap.toLinearMap e.symm.dualMap.injective (Projectivization.mk K a ha)) ↔ _
  rw [Projectivization.map_mk,Projectivization.map_mk,incident_mk_pair,incident_mk_pair]
  simp only [LinearEquiv.coe_coe,LinearEquiv.dualMap_apply,LinearEquiv.symm_apply_apply]

lemma incidences_coordinates (e : V≃ₗ[K]W) (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences (S.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding)=incidences S T := by
  have hh : (incidences (S.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_coordinates]
  exact_mod_cast hh

lemma decoded_coordinates (e : V≃ₗ[K]W) (U S : Finset (ℙ K V)) (Z : Finset (ℙ K W))
    (hZU : Z⊆U.map (projectiveEquiv e).toEmbedding) :
    let W₀ := Z.map (projectiveEquiv e).symm.toEmbedding
    W₀⊆U ∧ W₀.card=Z.card ∧ (W₀∩S).card=(Z∩S.map (projectiveEquiv e).toEmbedding).card := by
  dsimp only
  refine ⟨?_,Finset.card_map _,?_⟩
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp (hZU hz)
    simpa only [←he,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hy
  · have he : S=(S.map (projectiveEquiv e).toEmbedding).map (projectiveEquiv e).symm.toEmbedding := by
      ext x
      simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      constructor
      · intro hx
        exact ⟨projectiveEquiv e x,⟨x,hx,rfl⟩,(projectiveEquiv e).symm_apply_apply x⟩
      · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
        simpa only [Equiv.symm_apply_apply] using hy
    conv_lhs => rw [he]
    rw [←Finset.map_inter,Finset.card_map]

end

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometricRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma mk_normalized (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) :
    Projectivization.mk K (normalized f b p).val (normalized_nonzero f b p)=p.val.val := by
  rw [←p.val.val.mk_rep,Projectivization.mk_eq_mk_iff]
  exact ⟨_,rfl⟩

lemma normalized_injective (f : V→ₗ[K]W) (b : ℙ K W) :
    Function.Injective (normalized f b) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  rw [←mk_normalized f b p,←mk_normalized f b q]
  have hh := congrArg Subtype.val hpq
  congr 1

lemma affine_fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (w : W) : Nat.card {v : V // f v=w}≤Nat.card f.ker := by
  classical
  let : Finite V := Module.finite_of_finite K
  by_cases h : ∃v,f v=w
  · obtain ⟨v₀,hv₀⟩:=h
    let g : {v : V // f v=w}→f.ker := fun v=>⟨v.val-v₀,by
      rw [LinearMap.mem_ker,map_sub,v.property,hv₀,sub_self]⟩
    apply Nat.card_le_card_of_injective g
    intro a b hab
    apply Subtype.ext
    have hh := congrArg Subtype.val hab
    change a.val-v₀=b.val-v₀ at hh
    have hhh := congrArg (fun x : V=>x+v₀) hh
    simpa only [sub_add_cancel] using hhh
  · have hi : IsEmpty {v : V // f v=w} := ⟨fun v=>h ⟨v.val,v.property⟩⟩
    let := hi
    simp

theorem fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (b : ℙ K W) :
    Nat.card {p : Domain f // image f p=b}≤(Nat.card K)^(finrank K f.ker) := by
  let : Finite V := Module.finite_of_finite K
  have hh := (Nat.card_le_card_of_injective (normalized f b) (normalized_injective f b)).trans
    (affine_fiber_card_le f b.rep)
  have hn : Nat.card f.ker=(Nat.card K)^(finrank K f.ker) :=
    Module.natCard_eq_pow_finrank (K:=K)
  exact hh.trans_eq hn

theorem dual_restriction_fiber_card_le [Finite K] [FiniteDimensional K V]
    (U : Submodule K V) (b : ℙ K (Dual K U)) :
    Nat.card {p : Domain U.dualRestrict // image U.dualRestrict p=b}≤
      (Nat.card K)^(finrank K V-finrank K U) := by
  have hh := fiber_card_le U.dualRestrict b
  have hr := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hk : finrank K U.dualRestrict.ker=finrank K V-finrank K U := by
    change finrank K U.dualAnnihilator=_
    omega
  rwa [hk] at hh

end

open Module ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_restriction (U : Submodule K V) (x : ℙ K U)
    (p : Domain U.dualRestrict) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p.val ↔
      Incident x (image U.dualRestrict p) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident image
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker,Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K
    (U.dualRestrict p.val.rep) p.property
  rw [←ha]
  simp only [Units.smul_def,LinearMap.smul_apply,Submodule.dualRestrict_apply,
    smul_eq_mul,mul_eq_zero,Units.ne_zero,false_or,Submodule.subtype_apply]

lemma incident_of_zero_restriction (U : Submodule K V) (x : ℙ K U)
    (p : ℙ K (Dual K V)) (hp : U.dualRestrict p.rep=0) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  exact congrArg (fun f : Dual K U=>f v) hp

lemma restriction_nonzero_of_degree_lt
    (U : Submodule K V) (S : Finset (ℙ K U)) (p : ℙ K (Dual K V))
    (h : (S.filter fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p).card<S.card) :
    U.dualRestrict p.rep≠0 := by
  intro hp
  have he : S.filter (fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p)=S := by
    apply Finset.filter_eq_self.mpr
    intro x _
    exact incident_of_zero_restriction U x p hp
  rw [he] at h
  exact lt_irrefl _ h

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.DyadicLifts
open scoped Classical BigOperators
variable {A B : Type*}

lemma multiplicity_pos (f : A→B) (T : Finset A) {a : A} (ha : a∈T) :
    0 < multiplicity f T (f a) :=
  Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩

lemma multiplicity_mono (f : A→B) {T U : Finset A} (hTU : T⊆U) (b : B) :
    multiplicity f T b ≤ multiplicity f U b :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)

lemma bin_fiber (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    multiplicity f (bin f T k) b=multiplicity f T b := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hak := (Finset.mem_filter.mp ha).2
  unfold multiplicity
  congr 1
  ext x
  simp only [bin,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,_⟩,he⟩;exact ⟨hx,he⟩
  · rintro ⟨hx,he⟩;exact ⟨⟨hx,by rw [he];exact hak⟩,he⟩

lemma bin_multiplicity_bounds (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    2^k ≤ multiplicity f T b ∧ multiplicity f T b < 2*(2^k) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha,hk⟩ := Finset.mem_filter.mp ha
  have hp := multiplicity_pos f T ha
  constructor
  · rw [←hk];exact Nat.pow_log_le_self 2 (ne_of_gt hp)
  · have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (multiplicity f T (f a))
    rw [hk,pow_succ,mul_comm] at hh
    exact hh

lemma bin_mass_bounds (f : A→B) (T : Finset A) (k : ℕ) :
    2^k*(restrictions f T k).card ≤ (bin f T k).card ∧
      (bin f T k).card ≤ 2*(2^k)*(restrictions f T k).card := by
  have he : (bin f T k).card=∑b∈restrictions f T k,multiplicity f T b := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=restrictions f T k)
      (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)]
    apply Finset.sum_congr rfl
    intro b hb
    exact bin_fiber f T k hb
  rw [he]
  constructor
  · calc
      _ = ∑b∈restrictions f T k,2^k := by simp [mul_comm]
      _  ≤  _ := Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).1
  · calc
      _  ≤  ∑b∈restrictions f T k,2*(2^k) :=
        Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).2.le
      _ = _ := by simp [mul_comm]

lemma restrictions_subset_enclosure (f : A→B) {T U : Finset A} (hTU : T⊆U) (k : ℕ) :
    restrictions f T k⊆enclosure f U (2^k) := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_image.mpr ⟨a,hTU (Finset.mem_filter.mp ha).1,rfl⟩,
    (bin_multiplicity_bounds f T k hb).1.trans (multiplicity_mono f hTU _)⟩

lemma enclosure_mass (f : A→B) (U : Finset A) (l : ℕ) :
    l*(enclosure f U l).card ≤ U.card := by
  have hs : enclosure f U l⊆U.image f := Finset.filter_subset _ _
  calc
    _ = ∑b∈enclosure f U l,l := by simp [mul_comm]
    _  ≤  ∑b∈enclosure f U l,multiplicity f U b :=
      Finset.sum_le_sum fun b hb=> (Finset.mem_filter.mp hb).2
    _  ≤  ∑b∈U.image f,multiplicity f U b :=
      Finset.sum_le_sum_of_subset hs
    _ = U.card := (Finset.card_eq_sum_card_fiberwise (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)).symm

theorem exists_massive_bin (f : A→B) (T : Finset A) (M : ℕ)
    (hM : ∀a∈T,multiplicity f T (f a) ≤ M) :
    ∃ k ≤ Nat.log 2 M, T.card ≤ (Nat.log 2 M+1)*(bin f T k).card := by
  let keys := Finset.range (Nat.log 2 M+1)
  have maps : ∀a∈T,Nat.log 2 (multiplicity f T (f a))∈keys := by
    intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM a ha)))
  have hn : keys.Nonempty := ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hp : (0:ℝ) < keys.card := by exact_mod_cast Finset.card_pos.mpr hn
  obtain ⟨k,hk,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s:=T) (t:=keys) (f:=fun a=> Nat.log 2 (multiplicity f T (f a)))
    (b:=(T.card:ℝ)/keys.card) maps hn (by
      rw [nsmul_eq_mul,mul_div_cancel₀ _ (ne_of_gt hp)])
  refine ⟨k,Nat.le_of_lt_succ (Finset.mem_range.mp hk),?_⟩
  have hh : (T.card:ℝ) ≤ (keys.card:ℝ)*(bin f T k).card := by
    have := (div_le_iff₀ hp).mp hc
    simpa only [bin,mul_comm] using this
  have hkeys : keys.card=Nat.log 2 M+1 := Finset.card_range _
  rw [hkeys] at hh
  exact_mod_cast hh

end SharpRamseyFive.DyadicLifts

namespace SharpRamseyFive.ProjectiveRestriction
open Module DyadicLifts
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

lemma finite_lift_bound (U : Submodule K V) (T : Finset (Domain U.dualRestrict))
    (b : ℙ K (Dual K U)) :
    multiplicity (image U.dualRestrict) T b ≤ (Nat.card K)^(finrank K V-finrank K U) := by
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Finite (Domain U.dualRestrict) := by unfold Domain; infer_instance
  let f := image U.dualRestrict
  let A := T.filter fun p=>f p=b
  let g : A→{p : Domain U.dualRestrict // f p=b} := fun p=>⟨p.val,(Finset.mem_filter.mp p.prop).2⟩
  have hi : Function.Injective g := by
    intro a c hac
    have hh := congrArg (fun x : {p : Domain U.dualRestrict // f p=b}=>x.val) hac
    exact Subtype.ext hh
  have hn := Nat.card_le_card_of_injective g hi
  have he : Nat.card A=A.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [he] at hn
  exact hn.trans (dual_restriction_fiber_card_le U b)

theorem exists_restriction_dyad (U : Submodule K V)
    (T UT : Finset (Domain U.dualRestrict)) (hTU : T⊆UT) (hT : T.Nonempty) :
    ∃ k ≤ Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U)),
      2^k ≤ (Nat.card K)^(finrank K V-finrank K U) ∧
      T.card ≤ 2*(Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U))+1)*(2^k)*
        (restrictions (image U.dualRestrict) T k).card ∧
      restrictions (image U.dualRestrict) T k ⊆ enclosure (image U.dualRestrict) UT (2^k) ∧
      (2^k)*(enclosure (image U.dualRestrict) UT (2^k)).card ≤ UT.card ∧
      ∀b∈restrictions (image U.dualRestrict) T k,
        2^k ≤ multiplicity (image U.dualRestrict) T b ∧
        multiplicity (image U.dualRestrict) T b < 2*(2^k) := by
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let f := image U.dualRestrict
  have hl : ∀a∈T,multiplicity f T (f a) ≤ M := fun a _=>finite_lift_bound U T (f a)
  obtain ⟨k,hk,hc⟩ := exists_massive_bin f T M hl
  have hM : M≠0 := by
    obtain ⟨a,ha⟩ := hT
    exact ne_of_gt ((multiplicity_pos f T ha).trans_le (hl a ha))
  refine ⟨k,hk,Nat.pow_le_of_le_log hM hk,?_,
    restrictions_subset_enclosure f hTU k,enclosure_mass f UT (2^k),
    fun b hb=>bin_multiplicity_bounds f T k hb⟩
  have hm := (bin_mass_bounds f T k).2
  have hh := hc.trans (Nat.mul_le_mul_left (Nat.log 2 M+1) hm)
  simpa only [M,f,mul_assoc,mul_left_comm,mul_comm] using hh

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.FiniteRemoval
open scoped Classical BigOperators
variable {A : Type*}

theorem retain_card (T : Finset A) (d : A→ℝ) (c δ : ℝ) (hc : 0 < c)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ δ*c*T.card) :
    (1-δ)*(T.card:ℝ) ≤ (T.filter fun a=>d a ≤ c).card := by
  let G := T.filter fun a=>d a ≤ c
  let B := T.filter fun a=>c < d a
  have hpartition : G.card+B.card=T.card := by
    have he : B=T.filter (fun a=>¬d a ≤ c) := by simp only [B,not_le]
    rw [he]
    exact Finset.card_filter_add_card_filter_not _
  have hB : c*(B.card:ℝ) ≤ ∑a∈B,d a := by
    calc
      _ = ∑a∈B,c := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun a ha=>(Finset.mem_filter.mp ha).2.le
  have hBT : ∑a∈B,d a ≤ ∑a∈T,d a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a ha _=>hd a ha)
  have hcard : (G.card:ℝ)+(B.card:ℝ)=T.card := by exact_mod_cast hpartition
  have hbad : (B.card:ℝ) ≤ δ*T.card := by
    have hh := hB.trans (hBT.trans hsum)
    nlinarith
  change (1-δ)*(T.card:ℝ) ≤ (G.card:ℝ)
  nlinarith

theorem large_cell_retains_half (T : Finset A) (d : A→ℝ)
    (n s q τ : ℝ) (hq : 0 < q) (hs : 0 < s) (hτ : 0 < τ)
    (hsmall : Real.sqrt τ ≤ 1/200) (hsize : n ≤ 100*s)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ τ*n*T.card/q) :
    (T.card:ℝ)/2 ≤ (T.filter fun a=>d a ≤ Real.sqrt τ*s/q).card := by
  have hr : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hr2 := Real.sq_sqrt hτ.le
  have hc : 0 < Real.sqrt τ*s/q := div_pos (mul_pos hr hs) hq
  have hcs : τ*n/q ≤ (1/2:ℝ)*(Real.sqrt τ*s/q) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hq).mpr
    have hτn : τ*n ≤ τ*(100*s) := mul_le_mul_of_nonneg_left hsize hτ.le
    have hsτ : τ*(100*s) ≤ (1/2:ℝ)*(Real.sqrt τ*s) := by
      have hτr : τ ≤ Real.sqrt τ/200 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hτr hs.le
      nlinarith
    nlinarith
  have hh : ∑a∈T,d a ≤ (1/2:ℝ)*(Real.sqrt τ*s/q)*T.card := by
    calc
      _ ≤ τ*n*T.card/q := hsum
      _ = (τ*n/q)*T.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg _)
  have hz := retain_card T d (Real.sqrt τ*s/q) (1/2) hc hd hh
  linarith

end SharpRamseyFive.FiniteRemoval

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma goodLifts_nonzero (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (hκ : κ < 1) (hS : S.Nonempty)
    {p : ℙ K (Dual K V)} (hp : p∈goodLifts U S T κ) : U.dualRestrict p.rep≠0 := by
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hcut := (Finset.mem_filter.mp hp).2
  have hdeg : (flatDegree U S p:ℝ) < S.card := by nlinarith
  apply restriction_nonzero_of_degree_lt U S p
  exact_mod_cast hdeg

lemma card_nonzeroLifts (U : Submodule K V) (T : Finset (ℙ K (Dual K V)))
    (hT : ∀p∈T,U.dualRestrict p.rep≠0) : (nonzeroLifts U T).card=T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card=T.card
  rw [Finset.card_subtype,Finset.filter_eq_self.mpr hT]

lemma nonzeroLifts_mono (U : Submodule K V) {T UT : Finset (ℙ K (Dual K V))}
    (hTU : T⊆UT) : nonzeroLifts U T⊆nonzeroLifts U UT := Finset.subtype_mono hTU

lemma card_nonzeroLifts_le (U : Submodule K V) (T : Finset (ℙ K (Dual K V))) :
    (nonzeroLifts U T).card ≤ T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card ≤ T.card
  rw [Finset.card_subtype]
  exact Finset.card_filter_le _ _

lemma restricted_flatDegree (U : Submodule K V) (S : Finset (ℙ K U))
    (p : Domain U.dualRestrict) :
    (S.filter fun x=>Incident x (image U.dualRestrict p)).card=flatDegree U S p.val := by
  unfold flatDegree
  congr 1
  ext x
  simp only [Finset.mem_filter,incident_restriction]

lemma restricted_degree_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ)
    {b : ℙ K (Dual K U)}
    (hb : b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k) :
    ((S.filter fun x=>Incident x b).card:ℝ) ≤ κ*S.card := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
  have hpT : p∈nonzeroLifts U (goodLifts U S T κ) := (Finset.mem_filter.mp hp).1
  have hg : p.val∈goodLifts U S T κ := Finset.mem_subtype.mp hpT
  rw [restricted_flatDegree]
  exact (Finset.mem_filter.mp hg).2

lemma reduced_incidence_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ) :
    (incidences S (restrictions (image U.dualRestrict)
      (nonzeroLifts U (goodLifts U S T κ)) k):ℝ) ≤
      κ*S.card*(restrictions (image U.dualRestrict)
        (nonzeroLifts U (goodLifts U S T κ)) k).card := by
  rw [incidences_eq_sum]
  calc
    _ ≤ ∑b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k,
        κ*S.card := by
      apply Finset.sum_le_sum
      intro b hb
      have hh := restricted_degree_bound U S T κ k hb
      simpa only [Finset.sum_boole,incidenceEntry] using hh
    _ = _ := by simp [mul_comm]

end

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_restriction (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ : ℝ) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      2^k ≤ M ∧
      (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card ∧
      (restrictions (image U.dualRestrict) G k).Nonempty ∧
      restrictions (image U.dualRestrict) G k ⊆
        enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k) ∧
      ((enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card:ℝ)*T.card ≤
        4*L*UT.card*(restrictions (image U.dualRestrict) G k).card ∧
      n*T.card ≤ 400*L*M*S.card*(restrictions (image U.dualRestrict) G k).card := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hqpos : (0:ℝ) < Nat.card K := by linarith
  have hscard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htcard : (0:ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hκ : Real.sqrt τ/(Nat.card K) < 1 := by
    apply (div_lt_one hqpos).mpr
    linarith
  have hGcard : G.card=(goodLifts U S T (Real.sqrt τ/Nat.card K)).card :=
    card_nonzeroLifts U _ (fun p hp=>goodLifts_nonzero U S T _ hκ hS hp)
  have hhalf : (T.card:ℝ)/2 ≤ G.card := by
    rw [hGcard]
    have hh := large_cell_retains_half T (fun p=>(flatDegree U S p:ℝ))
      n S.card (Nat.card K) τ hqpos hscard hτ hsmall hsize
      (fun _ _=>Nat.cast_nonneg _) hsum
    simpa only [goodLifts,div_mul_eq_mul_div] using hh
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0:ℝ)<(T.card:ℝ)/2) hhalf)
  have hGUT : G⊆nonzeroLifts U UT :=
    nonzeroLifts_mono U ((Finset.filter_subset _ _).trans hTU)
  obtain ⟨k,hk,hkm,hm,hsub,hencl,hdyad⟩ := exists_restriction_dyad U G (nonzeroLifts U UT) hGUT hG
  have hm' : (G.card:ℝ) ≤ 2*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    exact_mod_cast hm
  have hmass : (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    linarith
  have h0 : (restrictions (image U.dualRestrict) G k).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have he : (restrictions (image U.dualRestrict) G k).card=0 := by omega
    rw [he,Nat.cast_zero,mul_zero] at hmass
    linarith
  refine ⟨k,hk,hkm,hmass,h0,hsub,?_,?_⟩
  · have he : (2:ℝ)^k*(enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card ≤ UT.card := by
      have hh := hencl.trans (card_nonzeroLifts_le U UT)
      exact_mod_cast hh
    have h1 := mul_le_mul_of_nonneg_left hmass
      (Nat.cast_nonneg (enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card)
    have h2 := mul_le_mul_of_nonneg_left he
      (by positivity : (0:ℝ) ≤ 4*L*(restrictions (image U.dualRestrict) G k).card)
    nlinarith
  · have hkm' : (2:ℝ)^k ≤ M := by exact_mod_cast hkm
    have h1 := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg T.card)
    have h2 := mul_le_mul_of_nonneg_left hmass
      (by positivity : (0:ℝ) ≤ 100*S.card)
    have h3 := mul_le_mul_of_nonneg_left hkm'
      (by positivity : (0:ℝ) ≤ 400*L*S.card*(restrictions (image U.dualRestrict) G k).card)
    nlinarith

end

open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators

lemma logarithmic_gap_of_cross {a b c d C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hC : 0 < C)
    (hcross : a*d ≤ C*c*b) :
    Real.log (a/b) ≤ Real.log (c/d)+Real.log C := by
  have hh : a/b ≤ C*(c/d) := by
    apply (div_le_iff₀ hb).mpr
    calc
      a  ≤  (C*c*b)/d := (le_div_iff₀ hd).mpr hcross
      _ = C*(c/d)*b := by ring
  have hl := Real.log_le_log (div_pos ha hb) hh
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (div_pos hc hd))] at hl
  linarith only [hl]

lemma restriction_product_loss (q n t s t₀ b L : ℝ) (D j : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hjd : j ≤ D)
    (horig : q^D*Real.exp (-b) ≤ n*t)
    (hred : n*t ≤ 400*L*q^(D-j)*s*t₀) :
    q^j*Real.exp (-(b+Real.log (400*L))) ≤ s*t₀ := by
  have hpow : 0 < q^(D-j) := pow_pos hq _
  have hmul : q^(D-j)*(q^j*Real.exp (-b)) ≤ q^(D-j)*(400*L*s*t₀) := by
    have he : q^D=q^(D-j)*q^j := by rw [←pow_add,Nat.sub_add_cancel hjd]
    rw [he] at horig
    nlinarith only [horig,hred]
  have hc : q^j*Real.exp (-b) ≤ 400*L*s*t₀ := (mul_le_mul_iff_of_pos_left hpow).mp hmul
  rw [neg_add,Real.exp_add,Real.exp_neg (Real.log (400*L)),Real.exp_log (by positivity)]
  rw [←mul_assoc,mul_inv_le_iff₀ (by positivity : (0:ℝ)<400*L)]
  nlinarith only [hc]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_pair_with_losses (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ b : ℝ) (hn : 0 < n) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (horig : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b) ≤ n*T.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      let T₀ := restrictions (image U.dualRestrict) G k
      let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K U)*Real.exp (-(b+Real.log (400*L))) ≤ (S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ) ≤ (Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ) ≤ Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card) ≤ Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      ∀u v : ℝ,0 < u → u ≤ v →
        Real.log (u/S.card) ≤ Real.log (v/n)+Real.log 100 := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  obtain ⟨k,hk,_,hm,hT₀,hsub,hgap,hprod⟩ :=
    large_cell_restriction U S T UT hS hT hTU n τ hτ hsmall hsize hsum
  let T₀ := restrictions (image U.dualRestrict) G k
  let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  have hL : (0:ℝ)<L := by dsimp [L];positivity
  have htc : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have ht₀ : (0:ℝ)<T₀.card := by exact_mod_cast hT₀.card_pos
  have hut : (0:ℝ)<UT.card := by exact_mod_cast (hT.card_pos.trans_le (Finset.card_le_card hTU))
  have hut₀ : (0:ℝ)<UT₀.card := by exact_mod_cast (hT₀.card_pos.trans_le (Finset.card_le_card hsub))
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp := restriction_product_loss (Nat.card K) n T.card S.card T₀.card b L
    (finrank K V) (finrank K U) hq hL (Submodule.finrank_le U) horig (by
      simpa only [M,Nat.cast_pow] using hprod)
  refine ⟨k,hk,hT₀,hsub,hp,fun p hp=>restricted_degree_bound U S T _ k hp,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (reduced_incidence_bound U S T (Real.sqrt τ/Nat.card K) k) hq.le
    calc
      _  ≤  (Nat.card K:ℝ)*(Real.sqrt τ/Nat.card K*S.card*T₀.card) := hh
      _ = _ := by field_simp;ring
  · exact logarithmic_gap_of_cross hut₀ ht₀ hut htc (by positivity : (0:ℝ)<4*L) hgap
  · intro u v hu huv
    apply logarithmic_gap_of_cross hu hs (hu.trans_le huv) hn (by norm_num : (0:ℝ)<100)
    have hh := mul_le_mul_of_nonneg_left hsize hu.le
    have hh' := mul_le_mul_of_nonneg_right huv (by positivity : (0:ℝ) ≤ 100*S.card)
    nlinarith only [hh,hh']

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence ProjectiveTraining
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma section_mono (A : Submodule K V) {X Y : Finset (ℙ K V)} (hXY : X⊆Y) :
    flatSection A X⊆flatSection A Y := by
  intro x hx
  simpa only [flatSection,Finset.mem_preimage] using hXY (Finset.mem_preimage.mp hx)

lemma range_flatEmbedding (A : Submodule K V) (p : ℙ K V) :
    p∈Set.range (flatEmbedding A) ↔ p.submodule≤A := by
  constructor
  · rintro ⟨x,rfl⟩
    induction x using Projectivization.ind with | h v hv =>
    change (Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K v hv)).submodule≤A
    rw [Projectivization.map_mk,Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact v.property
  · intro hp
    have hm : p.rep∈A := hp (by rw [p.submodule_eq]; exact Submodule.mem_span_singleton_self p.rep)
    have hn : (⟨p.rep,hm⟩:A)≠0 := fun hz=>p.rep_nonzero (congrArg Subtype.val hz)
    refine ⟨Projectivization.mk K (⟨p.rep,hm⟩:A) hn,?_⟩
    change Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K (⟨p.rep,hm⟩:A) hn)=p
    rw [Projectivization.map_mk]
    exact p.mk_rep

variable [Finite K] [FiniteDimensional K V]

lemma section_map (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).map (flatEmbedding A)=X∩flatPoints A := by
  ext x
  simp only [Finset.mem_map,flatSection,Finset.mem_preimage,Finset.mem_inter,mem_flatPoints]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,(range_flatEmbedding A _).mp ⟨a,rfl⟩⟩
  · rintro ⟨hx,hflat⟩
    obtain ⟨a,rfl⟩ := (range_flatEmbedding A x).mpr hflat
    exact ⟨a,hx,rfl⟩

lemma section_card (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).card=(X∩flatPoints A).card := by
  rw [←section_map,Finset.card_map]

lemma section_degree_sum (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)=incidences (X∩flatPoints A) T := by
  rw [←section_map,incidences_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_map]
  simp only [flatDegree, incidenceEntry, Finset.sum_boole]
  rfl

omit [Finite K] [FiniteDimensional K V] in
lemma incidences_mono_left {X Y : Finset (ℙ K V)} (T : Finset (ℙ K (Dual K V))) (hXY : X⊆Y) :
    incidences X T ≤ incidences Y T := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.product_subset_product hXY (Finset.Subset.refl _)

lemma section_density (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) (τ : ℝ)
    (h : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)≤τ*X.card*T.card/(Nat.card K) := by
  rw [section_degree_sum]
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  apply (le_div_iff₀ hq).mpr
  have hi : (incidences (X∩flatPoints A) T:ℝ) ≤ incidences X T := by
    exact_mod_cast incidences_mono_left T (Finset.inter_subset_left (s₁:=X) (s₂:=flatPoints A))
  nlinarith only [mul_le_mul_of_nonneg_left hi hq.le,h]

omit [Finite K] [FiniteDimensional K V] in
lemma section_decoder (A : Submodule K V) (X U : Finset (ℙ K V)) (Z : Finset (ℙ K A))
    (hZU : Z⊆flatSection A U) :
    Z.map (flatEmbedding A)⊆U ∧ (Z.map (flatEmbedding A)).card=Z.card ∧
    ((Z.map (flatEmbedding A))∩X).card=(Z∩flatSection A X).card := by
  refine ⟨?_,Finset.card_map _,?_⟩
  · rintro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp hx
    exact Finset.mem_preimage.mp (hZU hy)
  · have he : ((Z.map (flatEmbedding A))∩X)=(Z∩flatSection A X).map (flatEmbedding A) := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_map,flatSection,Finset.mem_preimage]
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,hx⟩
        exact ⟨y,⟨hy,hx⟩,rfl⟩
      · rintro ⟨y,⟨hy,hx⟩,rfl⟩
        exact ⟨⟨y,hy,rfl⟩,hx⟩
    rw [he,Finset.card_map]

end

open Module ProjectiveIncidence ProjectiveTraining DyadicLifts
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem original_large_cell (A : Submodule K V)
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hX : X.Nonempty) (hT : T.Nonempty) (hXU : X⊆UX) (hTU : T⊆UT)
    (τ b : ℝ) (hτ : 0<τ) (hsmall : Real.sqrt τ≤1/200)
    (hflat : (X.card:ℝ)≤100*(X∩flatPoints A).card)
    (hprod : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hdens : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    let S := flatSection A X
    let US := flatSection A UX
    let M := (Nat.card K)^(finrank K V-finrank K A)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
    S.Nonempty ∧ S⊆US ∧ S.card≤X.card ∧ (X.card:ℝ)≤100*S.card ∧
    ∃k≤Nat.log 2 M,
      let T₀ := restrictions (image A.dualRestrict) G k
      let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K A)*Real.exp (-(b+Real.log (400*L)))≤(S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ)≤(Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ)≤Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card)≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      Real.log ((US.card:ℝ)/S.card)≤Real.log ((UX.card:ℝ)/X.card)+Real.log 100 := by
  dsimp only
  have hx : (0:ℝ)<X.card := by exact_mod_cast hX.card_pos
  have hxs : (X.card:ℝ)≤100*(flatSection A X).card := by simpa only [section_card] using hflat
  have hs : (0:ℝ)<(flatSection A X).card := by nlinarith only [hx,hxs]
  have hS : (flatSection A X).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hs)
  have hSU := section_mono A hXU
  have hsX : (flatSection A X).card≤X.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  have huX : (flatSection A UX).card≤UX.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  obtain ⟨k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ := large_cell_pair_with_losses
    A (flatSection A X) T UT hS hT hTU X.card τ b hx hτ hsmall hxs hprod
    (section_density A X T τ hdens)
  refine ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,?_⟩
  apply hsgap (flatSection A UX).card UX.card
  · exact_mod_cast (hS.mono hSU).card_pos
  · exact_mod_cast huX

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_RestrictionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma dyadic_levels_le (q r : ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hq : (q:ℝ)=Real.exp σ) (hr : r ≤ 5) :
    (Nat.log 2 (q^r)+1:ℝ) ≤ (5/Real.log 2+1)*σ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : 0 ≤ σ := le_trans (by norm_num) hσ
  have hh := Real.natLog_le_logb (q^r) 2
  norm_num only [Nat.cast_ofNat] at hh
  have he : Real.logb (2:ℝ) ((q^r:ℕ):ℝ) = (r:ℝ)*σ/Real.log 2 := by
    rw [Real.logb,Nat.cast_pow,hq,Real.log_pow,Real.log_exp]
  rw [he] at hh
  have hr' : (r:ℝ)≤5 := by exact_mod_cast hr
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr' hs) hl.le
  calc
    _ ≤ (r:ℝ)*σ/Real.log 2+1 := by linarith only [hh]
    _ ≤ 5*σ/Real.log 2+σ := add_le_add hm hσ
    _ = _ := by ring

lemma root_density_scale {σ τ β : ℝ} {j d : ℕ} (hσ : 1≤σ) (hτ : 0≤τ)
    (hβ : 0≤β) (hj : 2≤j) (hjd : j<d)
    (h : τ≤σ^(-200*(2:ℝ)^(d-2)*β)) :
    Real.sqrt τ ≤ σ^(-200*(2:ℝ)^(j-2)*β) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hpow : (2:ℝ)^(j-2)*2≤(2:ℝ)^(d-2) := by
    rw [←pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have he : -200*(2:ℝ)^(d-2)*β ≤ 2*(-200*(2:ℝ)^(j-2)*β) := by
    have := mul_le_mul_of_nonneg_right hpow hβ
    nlinarith
  have h' := h.trans (Real.rpow_le_rpow_of_exponent_le hσ he)
  have hh : σ^(2*(-200*(2:ℝ)^(j-2)*β))=(σ^(-200*(2:ℝ)^(j-2)*β))^2 := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hs.le (-200*(2:ℝ)^(j-2)*β) 2)
  rw [hh] at h'
  exact (sq_le_sq₀ (Real.sqrt_nonneg τ) (Real.rpow_nonneg hs.le _)).mp
    (by simpa only [Real.sq_sqrt hτ] using h')

theorem eventually_restriction_overheads {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D R b Cb : ℝ) (q r : ℕ), Range η σ D R →
      (q:ℝ)=Real.exp σ → r≤5 → b≤Cb*D*σ^(6*beta η) →
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤D*σ^(6*beta η) ∧
      Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤P η σ D R ∧
      b+Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤(Cb+1)*D*σ^(6*beta η) := by
  let C : ℝ := 400*(5/Real.log 2+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hb : 0<7*beta η := mul_pos (by norm_num) (beta_pos hη)
  have hlog : Tendsto (fun σ : ℝ=>(Real.log C+Real.log σ)/σ^(7*beta η)) atTop (𝓝 0) := by
    have hc : Tendsto (fun σ : ℝ=>Real.log C/σ^(7*beta η)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hb)
    have hv := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
    simpa only [add_div,add_zero] using hc.add hv
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hh
  intro D R b Cb q r hr hq hd hbb
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbound : Real.log (400*(Nat.log 2 (q^r)+1:ℝ))≤σ^(7*beta η) := by
    have hl := Real.log_le_log (by positivity : (0:ℝ)<400*(Nat.log 2 (q^r)+1:ℝ))
      (mul_le_mul_of_nonneg_left (dyadic_levels_le q r σ hσ hq hd) (by norm_num : (0:ℝ)≤400))
    have he : 400*((5/Real.log 2+1)*σ)=C*σ := by dsimp [C];ring
    rw [he,Real.log_mul hC.ne' hs.ne'] at hl
    exact hl.trans (by simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hh.le)
  have hdlo : σ^(7*beta η)≤D*σ^(6*beta η) := by
    calc
      _ = σ^beta η*σ^(6*beta η) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hr.dlo (Real.rpow_nonneg hs.le _)
  have hp : σ^(7*beta η)≤P η σ D R :=
    (Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)).trans
      (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  refine ⟨hbound.trans hdlo,hbound.trans hp,?_⟩
  nlinarith only [hbb,hbound,hdlo]

end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RecursivePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma map_option_none (p : Law (Option α)) (f : α→β) : map p (Option.map f) none=p none := by
  simp only [map,Fintype.sum_option,Option.map_none,ite_true,Option.map_some,
    Option.some_ne_none,ite_false,Finset.sum_const_zero,add_zero]
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveTraining
open Module
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]

omit [Finite K] [FiniteDimensional K V] [Fintype V] in
lemma exists_flat_finrank (d : ℕ) (hd : d≤finrank K V) :
    ∃A : Submodule K V,finrank K A=d := by
  obtain ⟨s,hn,hs⟩ := exists_finset_linearIndependent_of_le_finrank (R:=K) (M:=V) hd
  refine ⟨Submodule.span K (s:Set V),?_⟩
  have hspan : Set.range (fun x : s => (x:V))=(s:Set V) := by ext x;simp
  rw [←hspan,finrank_span_eq_card hs,Fintype.card_coe,hn]

omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_cover (d : ℕ) (A : Submodule K V) (hA : finrank K A=d) :
    ∃i∈flatIndices (K:=K) (V:=V) d,flatEnumeration i=A := by
  let i := Fintype.equivFin (Submodule K V) A
  have he : flatEnumeration i=A := (Fintype.equivFin _).symm_apply_apply A
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he,hA]⟩,he⟩
omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_nonempty (d : ℕ) (hd : d≤finrank K V) :
    (flatIndices (K:=K) (V:=V) d).Nonempty := by
  obtain ⟨A,hA⟩ := exists_flat_finrank d hd
  obtain ⟨i,hi,_⟩ := flatIndices_cover d A hA
  exact ⟨i,hi⟩
end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GenericFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open MeasureTheory
open scoped Classical BigOperators
variable {Ω α β : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α] [DecidableEq α] [Fintype β]

omit [DecidableEq α] in
lemma finiteImageLaw_map (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) (g : α→β) :
    map (finiteImageLaw μ f) g=finiteImageLaw μ (g∘f) := by
  apply Law.ext
  funext b
  have hh := finiteImageLaw_event μ f (Finset.univ.filter fun a=>g a=b)
  change (∑ a, if g a=b then finiteImageLaw μ f a else 0)=μ.real {ω | g (f ω)=b}
  simpa only [eventMass,Finset.sum_filter,Finset.mem_filter,Finset.mem_univ,true_and,
    Set.mem_ofPred_eq,Function.comp_apply] using hh

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_exact (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    (baseFiniteEncoded S U P τ (baseMessageDecoded U P τ R L₀ t)).map
        (baseMessageDecoded U P τ R L₀ t)=baseOutcome S U P τ R L₀ t := by
  simp only [baseFiniteEncoded,baseTableEncoded,baseOutcome,Option.map_map]
  rfl

omit [Finite K] [FiniteDimensional K V] in
theorem baseFinite_law (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    map (baseTableLaw U P τ R L₀) (fun t=>(baseFiniteEncoded S U P τ t).map t)=
      baseCaptureLaw S U P τ R L₀ := by
  rw [baseTableLaw,publicTableLaw,finiteImageLaw_map]
  unfold baseCaptureLaw
  congr 1
  funext t
  exact baseFinite_exact S U P τ R L₀ t

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_header (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) : m.1.val=S.card := by
  obtain ⟨x,hx,he⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun z : BaseMessage U P τ=>z.1.val) he.symm
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype V] in
lemma scoredEncoded_exact (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) :
    (scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t)=
      scoredOutcome X U n (messageOwn code) (messageBase code L₀) P τ c a R t := by
  simp only [scoredEncoded,scoredOutcome,Option.map_map]
  rfl

lemma scoredEncoded_law (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) :
    finiteImageLaw (baseTapeMeasure U P τ R L₀)
      (fun t=>(scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t))=
      scoredCaptureLaw X U n (messageOwn code) (messageBase code L₀) P τ c a R L₀ := by
  simp only [scoredEncoded_exact,scoredCaptureLaw]

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem scoreFinite_law (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) :
    map (scoreTableLaw U σ P τ R L₀)
      (fun t=>(scoreFiniteEncoded X U n σ P τ c a code t).map t)=
      scoredCaptureLaw X U n (messageOwn code) (messageBase code L₀) P τ c a R L₀ := by
  rw [scoreTableLaw,publicTableLaw,finiteImageLaw_map]
  exact scoredEncoded_law X U n σ P τ c a R L₀ code
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ScoreFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype V] in
lemma scoreFinite_header (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : ScoreTable U σ P τ) (m : ScoredMessage U σ P τ)
    (hm : scoreFiniteEncoded X U n σ P τ c a code t=some m) : m.1=n := by
  obtain ⟨z,_,hz⟩ := Option.map_eq_some_iff.mp hm
  exact congrArg (fun y : ScoredMessage U σ P τ=>y.1) hz.symm

omit [Finite K] [FiniteDimensional K V] in
lemma scoreFinite_cost_of_header (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a B : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (hcost : Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U n σ P τ):ℝ)≤B)
    (t : ScoreTable U σ P τ) (m : ScoredMessage U σ P τ)
    (hm : scoreFiniteEncoded X U n σ P τ c a code t=some m) : scoreFiniteCost U σ P τ m≤B := by
  unfold scoreFiniteCost
  rw [scoreFinite_header X U n σ P τ c a code t m hm]
  exact hcost

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  {Ω : ι→Type*} [∀i,Fintype (Ω i)] {M : ∀i,Ω i→Type*}

theorem branch_output_law (p : ∀i,Law (Ω i)) (i : ι)
    (encode : ∀t : Ω i,Option (M i t)) (decode : ∀i t,M i t→α) :
    map (piLaw p) (fun t=>(branchEncoded i encode t).map (branchDecoded decode t))=
      map (p i) (fun t=>(encode t).map (decode i t)) := by
  have hh := congrArg (fun q=>map q (fun t=>(encode t).map (decode i t))) (piLaw_eval p i)
  rw [map_comp] at hh
  simpa only [branchEncoded,branchDecoded,Option.map_map,Function.comp_def] using hh

omit [Fintype ι] [DecidableEq ι] [∀index,Fintype (Ω index)] in
lemma branch_sent (i : ι) (encode : ∀t : Ω i,Option (M i t))
    (t : ∀i,Ω i) (m : BranchMessage (M:=M) t)
    (hm : branchEncoded i encode t=some m) :
    ∃z,encode (t i)=some z ∧ Sigma.mk i z=m := Option.map_eq_some_iff.mp hm
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SmallFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem smallFinite_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    baseFiniteCost U P τ m≤110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  unfold baseFiniteCost
  rw [baseFinite_header S U P τ t m hm,baseAlphabet_small_card U S.card P τ hn]
  have hcost := (small_set_description S U hSU (Nat.card K:ℝ) P hn).2
  have hh := projective_header_le σ hσ hq hd
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have htotal : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
    apply (le_mul_of_one_le_right (by positivity) hP).trans
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hcost' : 100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+1)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith only [hcost,hh,htotal,hcost']
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_plane_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
      [Fintype (ℙ K (Dual K (Dual K A)))]
      [∀x : ℙ K A,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K A),Fintype (RadialLine x)],
    ∀ (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      let S := flatSection A X
      let US := flatSection A UX
      let M := (Nat.card K)^(finrank K V-finrank K A)
      let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
      ∃ k, k≤Nat.log 2 M ∧
      let T₀ := restrictions (image A.dualRestrict) G k
      let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
      ∃ n : Fin (1000*(Nat.card K)^2+1),
        n.val=reverseLength (Nat.card K) (Real.log ((US.card:ℝ)/S.card)) ∧
        let P₀ := P η σ D R
        let H := 1000*(Nat.card K)^2
        let encode := twoPublicEncoded S US T₀ UT₀ P₀ (Real.sqrt τ) H n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P₀))
        let decode := fun t m=>(twoPublicDecoded US UT₀ P₀ (Real.sqrt τ) H (Nat.card K) t m).map (flatEmbedding A)
        let p := map (twoPublicLaw US UT₀ P₀ (Real.sqrt τ) R L₀ H (Nat.card K))
          (fun t=>(encode t).map (decode t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m, encode t=some m → twoPublicCost US UT₀ P₀ (Real.sqrt τ) H (Nat.card K) t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)<(1:ℝ)/200 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_two_public_complete hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  have htroot : Real.sqrt τ≤σ^(-200*beta η) := by
    have hh := root_density_scale (j:=2) (d:=3) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(3-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    simpa using hh
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  dsimp only
  refine ⟨k,hk,?_⟩
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  have hov := hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) := hov.2.2
  have hp' : (Nat.card K:ℝ)^3*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨n,hn,hfail,hgood,hcost⟩ := hbase D B (Real.sqrt τ) R L₀ K A S US T₀ UT₀ hT₀ hA hq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  refine ⟨n,hn,?_,?_,?_⟩
  · have hm := map_option_none
      (map (twoPublicLaw US UT₀ (P η σ D R) (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K))
        (fun t=>(twoPublicEncoded S US T₀ UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P η σ D R)) t).map
          (twoPublicDecoded US UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t)))
      (fun Z=>Z.map (flatEmbedding A))
    rw [FiniteEntropy.map_comp] at hm
    simpa only [Function.comp_def,Option.map_map] using hm.le.trans hfail
  · intro W hW
    let tape := twoPublicLaw US UT₀ (P η σ D R) (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K)
    let encode := twoPublicEncoded S US T₀ UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P η σ D R))
    let decode := twoPublicDecoded US UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K)
    let pp := map tape (fun t=>(encode t).map (decode t))
    have hw' : 0 < map pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) := by
      dsimp only [pp]
      rw [FiniteEntropy.map_comp]
      simpa only [Function.comp_def,Option.map_map] using hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hw'
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
      subst W
      have hz := hgood Z hZ
      obtain ⟨hu,hcard,hcap⟩ := section_decoder A X UX Z hz.1
      refine ⟨hu,?_,?_⟩
      · rw [hcard]
        exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
      · rw [hcap,Finset.inter_comm]
        have hc := hz.2.2
        nlinarith only [hc,hxs]
  · intro t m hm
    have hc := hcost t m hm
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow hσ (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
    have hlog : Real.log (400*(Nat.log 2 M+1:ℝ))≤P η σ D R := hov.2.1
    have h100 : Real.log (100:ℝ)≤P η σ D R := (Real.log_le_log (by norm_num) (by
      have hn : (0:ℝ)≤Nat.log 2 M := by positivity
      linarith : (100:ℝ)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have h4 : Real.log (4*(Nat.log 2 M+1:ℝ))≤P η σ D R :=
      (Real.log_le_log (by positivity) (by
        have hn : (0:ℝ)≤Nat.log 2 M := by positivity
        linarith : (4:ℝ)*(Nat.log 2 M+1)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have hgX : 0≤Real.log ((UX.card:ℝ)/X.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
        simpa using (show (X.card:ℝ)≤UX.card by exact_mod_cast Finset.card_le_card hXU)))
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
        simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
    have hsum : Real.log ((US.card:ℝ)/S.card)+Real.log ((UT₀.card:ℝ)/T₀.card)+P η σ D R≤
        3*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      simp only [Nat.cast_add,Nat.cast_one] at hgap
      change _≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*(Nat.log 2 M+1:ℝ)) at hgap
      change _≤Real.log ((UX.card:ℝ)/X.card)+Real.log (100:ℝ) at hsgap
      linarith
    have hm' := mul_le_mul_of_nonneg_left hsum
      (by positivity : (0:ℝ)≤1300*(Nat.card K:ℝ)*P η σ D R)
    have hpos : 0≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by positivity
    nlinarith only [hc,hm',hpos]
end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlanePublicDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
variable (A : Submodule K V) [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
  [Fintype (ℙ K (Dual K (Dual K A)))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma planePublic_encoded_eq (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (n : Fin (1000*(Nat.card K)^2+1))
    (hn : n.val=reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))) :
    planePublicEncoded A X UX T UT P τ k=
      twoPublicEncoded (flatSection A X) (flatSection A UX) (planeHidden A X T τ k) (planeEnclosure A UT k)
        P (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/(planeHidden A X T τ k).card)
        (((planeHidden A X T τ k).card:ℝ)*Real.exp (2*P)) := by
  funext t
  unfold planePublicEncoded
  have hb : reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))≤1000*(Nat.card K)^2 := by
    rw [←hn]; exact Nat.le_of_lt_succ n.prop
  rw [dite_eq_left hb]
  congr 1
  exact Fin.ext hn.symm
end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_plane_public {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
      [Fintype (ℙ K (Dual K (Dual K A)))]
      [∀x : ℙ K A,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K A),Fintype (RadialLine x)],
    ∀ (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let P₀ := P η σ D R
        let p := map (planePublicLaw A UX UT P₀ τ R L₀ k)
          (fun t=>(planePublicEncoded A X UX T UT P₀ τ k t).map (planePublicDecoded A UX UT P₀ τ k t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,planePublicEncoded A X UX T UT P₀ τ k t=some m →
          planePublicCost A UX UT P₀ τ k t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_plane_public_complete hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  obtain ⟨k,hk,n,hn,hfail,hgood,hcost⟩ := hh D b τ R L₀ K V A X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  refine ⟨k,hk,?_⟩
  dsimp only
  rw [planePublic_encoded_eq A X UX T UT (P η σ D R) τ k n hn]
  exact ⟨hfail,hgood,hcost⟩
end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreePublicDefs
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instFintypeThreeLocalMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

lemma threePublic_law (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (br : ThreePublicIndex K σ) :
    map (threePublicLaw U UT σ P τ R L₀)
      (fun t=>(threePublicEncoded X U T UT σ P τ br t).map (threePublicDecoded U UT σ P τ t))=
    map (threeLocalLaw U UT σ P τ R L₀ br)
      (fun t=>(threeLocalEncoded X U T UT σ P τ br t).map (threeLocalDecoded U UT σ P τ br t)) :=
  branch_output_law _ br _ _
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ThreeHeader
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instFintypeThreeLocalMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization

private lemma log_three_sum {x y z : ℝ} (hx : 1≤x) (hy : 1≤y) (hz : 0≤z) (hzy : z≤y) :
    Real.log (1+(x+z))≤Real.log 3+Real.log x+Real.log y := by
  have hxy : x≤x*y := le_mul_of_one_le_right (by linarith) hy
  have hyx : y≤x*y := le_mul_of_one_le_left (by linarith) hx
  have h1 : 1≤x*y := hx.trans hxy
  have hh := Real.log_le_log (by positivity : 0<1+(x+z))
    (show 1+(x+z)≤3*x*y by linarith)
  rw [Real.log_mul (by positivity) (by linarith),Real.log_mul (by norm_num) (by linarith)] at hh
  exact hh

theorem threePublic_header {K : Type} [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] (σ : ℝ) (hσ : 100000≤σ)
    (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)≤35*(Nat.card K:ℝ) := by
  have hd : finrank K (Fin 4→K)≤5 := by simp
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  have hh := projective_header_le (K:=K) (V:=Fin 4→K) σ (by linarith) hq hd
  have ht := log_card_training_le (V:=Fin 4→K) σ hσ (vector_card_le_exp σ hq hd)
  rw [hq,Nat.card_eq_fintype_card] at ht
  let a : ℕ := (Fintype.card (ℙ K (Fin 4→K))+1)*
    Fintype.card (TrainingCode (Fin 4→K) (listCap σ) (productCap σ) (Nat.card (Fin 4→K)))
  let c : ℕ := Fintype.card (Submodule K (Fin 4→K))
  let l : ℕ := Nat.log 2 (Nat.card K)+1
  have ha1 : (1:ℝ)≤a := by
    have h : 0<a := Nat.mul_pos (Nat.succ_pos _) Fintype.card_pos
    exact_mod_cast h
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast Fintype.card_pos (α:=Submodule K (Fin 4→K))
  have hl1 : (1:ℝ)≤l := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.log 2 (Nat.card K)))
  have ha : Real.log (a:ℝ)≤7*(Nat.card K:ℝ) := by
    dsimp only [a]
    rw [Nat.cast_mul,Real.log_mul (by positivity) (by exact_mod_cast (Fintype.card_pos (α:=TrainingCode (Fin 4→K) (listCap σ) (productCap σ) (Nat.card (Fin 4→K)))).ne')]
    push_cast at hh ⊢
    linarith
  have hvc := vector_card_le_exp (K:=K) (V:=Fin 4→K) σ hq hd
  have hc : Real.log (c:ℝ)≤25*(Nat.card K:ℝ) := by
    have hsc := FlatAtlas.card_submodules_le (K:=K) (V:=Fin 4→K) 5 hd
    rw [Nat.card_eq_fintype_card] at hsc
    have hsc' : (c:ℝ)≤(Nat.card (Fin 4→K):ℝ)^5 := by exact_mod_cast hsc
    have he : (Real.exp (5*σ))^5=Real.exp (25*σ) := by
      rw [←Real.exp_nat_mul];congr 1;ring
    have hle := hsc'.trans ((pow_le_pow_left₀ (by positivity) hvc 5).trans_eq he)
    have hh' := Real.log_le_log (by linarith : (0:ℝ) < c) hle
    rw [Real.log_exp] at hh'
    linarith
  have hl : Real.log (l:ℝ)≤Nat.card K := by
    have hlq : (l:ℝ)≤(Nat.card K:ℝ)+1 := by
      dsimp only [l];rw [Nat.cast_add,Nat.cast_one]
      have hx : (Nat.log 2 (Nat.card K):ℝ)≤Nat.card K := by exact_mod_cast Nat.log_le_self 2 (Nat.card K)
      linarith only [hx]
    have hh' := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<l)
    linarith
  let z : ℕ := (flatIndices (K:=K) (V:=Fin 4→K) 3).card*l
  have hz : (z:ℝ)≤(c:ℝ)*l := by
    have hf : (flatIndices (K:=K) (V:=Fin 4→K) 3).card ≤ c := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have hz' : z ≤ c*l := Nat.mul_le_mul_right l hf
    exact_mod_cast hz'
  have hs := log_three_sum ha1 (one_le_mul_of_one_le_of_one_le hc1 hl1) (Nat.cast_nonneg z) hz
  have hcl : Real.log ((c:ℝ)*l)≤26*(Nat.card K:ℝ) := by
    rw [Real.log_mul (by linarith) (by linarith)];linarith
  have h3 : Real.log 3≤2 := by
    have hh' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have he : (Fintype.card (ThreePublicIndex K σ):ℝ)=1+((a:ℝ)+z) := by
    simp only [ThreePublicIndex,ThreeBranch,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,
      Fintype.card_fin,Fintype.card_coe,Nat.cast_add,Nat.cast_one,Nat.cast_mul,a,z,l]
  rw [he]
  linarith
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeLocal
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instFintypeThreeLocalMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_local_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      ∃br : ThreePublicIndex K σ,
        let P₀ := P η σ D R
        let p := map (threeLocalLaw U UT σ P₀ τ R L₀ br)
          (fun t=>(threeLocalEncoded X U T UT σ P₀ τ br t).map (threeLocalDecoded U UT σ P₀ τ br t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threeLocalEncoded X U T UT σ P₀ τ br t=some m →
          threeLocalCost U UT σ P₀ τ br t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_small_protocol hη hη' Cb hCb,
    eventually_plane_public hη hη' Cb hCb,eventually_ge_atTop (100000:ℝ)] with σ hscore hplane hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  have hσ1 : 1≤σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ1 (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := by linarith
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hd : finrank K (Fin 4→K)=4 := by rw [Module.finrank_pi];simp
  have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
  have hX : X.Nonempty := by
    have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^4*Real.exp (-b)) hprod
    exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
  have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
      simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
  have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
      simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
  have hcost_le (C : ℝ) (hC : 0≤C) (hC' : C≤4000) :
      C*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R)≤
      4000*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' hqpos.le) hP0) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  by_cases hn : (X.card:ℝ)≤100*(Nat.card K:ℝ)*P η σ D R
  · refine ⟨.inl (),?_,?_,?_⟩
    · change (map (baseTableLaw U (P η σ D R) τ R L₀) (fun t=>(baseFiniteEncoded X U (P η σ D R) τ t).map t)) none ≤ _
      rw [baseFinite_law]
      exact (baseSmallLaw X U hXU (P η σ D R) τ hP hn R L₀).1.trans (by positivity)
    · change ∀W,0 < (map (baseTableLaw U (P η σ D R) τ R L₀) (fun t=>(baseFiniteEncoded X U (P η σ D R) τ t).map t)) (some W) → _
      rw [baseFinite_law]
      intro W hW
      have hw := baseCaptureLaw_positive X U (P η σ D R) τ R L₀ W hW
      refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
    · intro t m hm
      exact (smallFinite_cost σ hσ1 hq.symm (by omega) X U hX hXU _ τ hP hn t m hm).trans (hcost_le 110 (by norm_num) (by norm_num))
  · let F := flatIndices (K:=K) (V:=Fin 4→K) 3
    have hF : F.Nonempty := flatIndices_nonempty 3 (by omega)
    let Flat := flatEnumeration (K:=K) (V:=Fin 4→K)
    have hFlat : ∀j∈F,finrank K (Flat j)=3 := flatIndices_rank 3
    have hcover : ∀A : Submodule K (Fin 4→K),finrank K A=3 → ∃j∈F,Flat j=A := flatIndices_cover 3
    let g := Real.log (X.card:ℝ)-3*σ/2
    have hXexp : (X.card:ℝ)=Real.exp (3*σ/2+g) := by
      dsimp only [g]
      rw [show 3*σ/2+(Real.log (X.card:ℝ)-3*σ/2)=Real.log (X.card:ℝ) by ring,Real.exp_log (by exact_mod_cast hX.card_pos)]
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    have ht : 0<t := by dsimp [t];positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    by_cases hsmall : ∀i,(C i).card≤(S.card:ℝ)/25
    · have hτhi' := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ1
        (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
      obtain ⟨_,_,hc,c,hf,hg⟩ := hscore D b τ g R L₀ q K (Fin 4) _ F hF Flat X U T
        hcard hσq (by simp) hr hL hb hbhi hτ hτhi' hXU hXT hdens hprod hXexp (lt_of_not_ge hn) hFlat hcover hsmall
      let n : Fin (Fintype.card (ℙ K (Fin 4→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
      have he : map (scoreTableLaw U σ (P η σ D R) τ R L₀)
          (fun t => (scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)=
        finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
          (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/20) 10 R L₀ c t).map
            (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t)) := by
        rw [scoreFinite_law,scoredEncoded_law]
      refine ⟨.inr (.inl (n,c)),?_,?_,?_⟩
      · change (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) none ≤ _
        rw [he]
        exact hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))])
      · change ∀W,0 < (map (scoreTableLaw U σ (P η σ D R) τ R L₀) (fun t=>(scoreFiniteEncoded X U n σ (P η σ D R) τ (9/20) 10 c t).map t)) (some W) → _
        rw [he]
        intro W hW
        obtain ⟨hWU,hsize,hcap⟩ := hg W hW
        exact ⟨hWU,hsize,(mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/20) (Nat.cast_nonneg _)).trans hcap⟩
      · intro t z hz
        exact (scoreFinite_cost_of_header X U n σ (P η σ D R) τ (9/20) 10 _ c hc t z hz).trans (hcost_le 100 (by norm_num) (by norm_num))
    · have hSX : S⊆X := peel_subset _ F hF _ X _ _
      have hret' : X.card≤2*S.card := peel_half _ F hF _ X _ _
      have hret : X.card≤4*S.card := by omega
      obtain ⟨a,ha,hlarge⟩ := large_clipped_part X S X hSX hret F hF (fun j=>flatPoints (Flat j)) m hsmall
      let : Finite (Dual K (Flat a)) := Module.finite_of_finite K
      let : ∀ x : ℙ K (Flat a),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
      let : ∀ x : ℙ K (Dual K (Flat a)),Fintype (RadialLine x) := fun _=>Fintype.ofFinite _
      obtain ⟨k,hk,hf,hg,hc⟩ := hplane D b τ R L₀ K (Fin 4→K) (Flat a) X U T UT
        (hFlat a ha) (by omega) hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens (by simpa only [hd] using hprod) hlarge
      have hk' : k≤Nat.log 2 (Nat.card K) := by simpa only [hd,hFlat a ha,Nat.reduceSub,pow_one] using hk
      refine ⟨.inr (.inr (⟨a,ha⟩,⟨k,Nat.lt_succ_of_le hk'⟩)),hf,?_,hc⟩
      intro W hW
      obtain ⟨hWU,hsize,hcap⟩ := hg W hW
      refine ⟨hWU,hsize.trans ?_,hcap⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreePublic
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instFintypeThreeLocalMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_three_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      ∃br : ThreePublicIndex K σ,
        let P₀ := P η σ D R
        let p := map (threePublicLaw U UT σ P₀ τ R L₀)
          (fun t=>(threePublicEncoded X U T UT σ P₀ τ br t).map (threePublicDecoded U UT σ P₀ τ t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threePublicEncoded X U T UT σ P₀ τ br t=some m →
          threePublicCost U UT σ P₀ τ t m≤
          4100*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_local_complete hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  obtain ⟨br,hf,hg,hc⟩ := hh D b τ R L₀ q K X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  refine ⟨br,?_,?_,?_⟩
  ·
    rw [threePublic_law]
    exact hf
  ·
    rw [threePublic_law]
    exact hg
  · intro t m hm
    obtain ⟨z,hz,rfl⟩ := branch_sent br (threeLocalEncoded X U T UT σ (P η σ D R) τ br) t m hm
    change Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)+
      threeLocalCost U UT σ (P η σ D R) τ br (t br) z≤_
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
    have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
    have hqpos : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos σ
    have hX : X.Nonempty := by
      have hp : 0<(X.card:ℝ)*T.card := lt_of_lt_of_le (by positivity : (0:ℝ)<(Nat.card K:ℝ)^4*Real.exp (-b)) hprod
      exact Finset.card_pos.mp (Nat.cast_pos.mp (pos_of_mul_pos_left hp (Nat.cast_nonneg _)))
    have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hX.card_pos hXT)
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
        simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
    have hgX : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
        simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
    have hbase : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      apply (le_mul_of_one_le_right hqpos.le hP).trans
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    have hl := threePublic_header (K:=K) σ hσ hq.symm
    have hz' := hc (t br) z hz
    nlinarith only [hz',hl,hbase]
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

lemma threeCertifiedBranch_spec (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (h : ∃br,ThreeCertified X U T UT σ P τ R L₀ br) :
    ThreeCertified X U T UT σ P τ R L₀ (threeCertifiedBranch X U T UT σ P τ R L₀) := by
  unfold threeCertifiedBranch
  rw [dite_eq_left h]
  exact h.choose_spec

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_three_certified {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K : Type) [Field K] [Finite K] [Fintype K] [CharP K q]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀x : ℙ K (Fin 4→K),Fintype (RadialLine x)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (X U : Finset (ℙ K (Fin 4→K))) (T UT : Finset (ℙ K (Dual K (Fin 4→K)))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let P₀ := P η σ D R
        let p := threeCertifiedLaw X U T UT σ P₀ τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,threeCertifiedEncoded X U T UT σ P₀ τ R L₀ t=some m →
          threePublicCost U UT σ P₀ τ t m≤
          4100*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_three_public_complete hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K _ _ _ _ _ _ _ _ _ _ X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  exact threeCertifiedBranch_spec X U T UT σ (P η σ D R) τ R L₀
    (hh D b τ R L₀ q K X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod)
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeCoordinateCertified
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instFintypeThreeLocalMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma threeCoordinateCertified_exact (e : V≃ₗ[K](Fin 4→K)) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    threeCoordinateCertifiedLaw e σ X U T UT P τ R L₀=
    map (threeCertifiedLaw (X.map (projectiveEquiv e).toEmbedding)
      (U.map (projectiveEquiv e).toEmbedding)
      (T.map (projectiveEquiv e.symm.dualMap).toEmbedding)
      (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀)
      (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding) := by
  simp only [threeCoordinateCertifiedLaw,threeCoordinatePublicLaw,threeCoordinateEncoded,
    threeCertifiedLaw,map_comp,Option.map_map,Function.comp_def]
  rfl

theorem eventually_three_coordinates_certified_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [Fintype K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
      [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))],
    ∀ (e : V≃ₗ[K](Fin 4→K))
      (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X⊆U → T⊆UT → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
        let p := threeCoordinateCertifiedLaw e σ X U T UT (P η σ D R) τ R L₀
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound X U (9/1000) ((X.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,threeCoordinateEncoded e X U T UT σ (P η σ D R) τ R L₀ t=some m →
          threeCoordinateCost e U UT σ (P η σ D R) τ t m≤
            4100*(Nat.card K:ℝ)*(P η σ D R)*
              (Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  filter_upwards [eventually_three_certified hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ e X U T UT hcard hσq hr hL hb hbhi hτ hτhi hXU hTU hXT hdens hprod
  let X' := X.map (projectiveEquiv e).toEmbedding
  let U' := U.map (projectiveEquiv e).toEmbedding
  let T' := T.map (projectiveEquiv e.symm.dualMap).toEmbedding
  let UT' := UT.map (projectiveEquiv e.symm.dualMap).toEmbedding
  have hXU' : X'⊆U' := Finset.map_subset_map.mpr hXU
  have hTU' : T'⊆UT' := Finset.map_subset_map.mpr hTU
  have hdens' : (Nat.card K:ℝ)*(incidences X' T':ℝ)≤τ*X'.card*T'.card := by
    simpa only [X',T',incidences_coordinates,Finset.card_map] using hdens
  have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(X'.card:ℝ)*T'.card := by
    simpa only [X',T',Finset.card_map] using hprod
  let (x : ℙ K (Fin 4→K)) : Fintype (RadialLine x) := Fintype.ofFinite _
  obtain ⟨hf,hg,hc⟩ := hh D b τ R L₀ q K X' U' T' UT' hcard hσq hr hL hb hbhi hτ hτhi hXU' hTU'
    (by simpa only [X',T',Finset.card_map] using hXT) hdens' hprod'
  let pp := threeCertifiedLaw X' U' T' UT' σ (P η σ D R) τ R L₀
  refine ⟨?_,?_,?_⟩
  · rw [threeCoordinateCertified_exact]
    rw [map_option_none]
    exact hf
  · intro W hW
    rw [threeCoordinateCertified_exact] at hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (projectiveEquiv e).symm.toEmbedding) (some W) hW
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (projectiveEquiv e).symm.toEmbedding=W := Option.some.inj he
      subst W
      have hz := hg Z hZ
      obtain ⟨hU,hcard',hcap⟩ := decoded_coordinates e U X Z hz.1
      refine ⟨hU,?_,?_⟩
      · simpa only [hcard',X',Finset.card_map] using hz.2.1
      · rw [Finset.inter_comm,hcap,Finset.inter_comm]
        simpa only [X',Finset.card_map,Finset.inter_comm] using hz.2.2
  · intro t m hm
    have hh := hc t m hm
    simpa only [threeCoordinateCost,U',X',T',UT',Finset.card_map] using hh
end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified_oai
