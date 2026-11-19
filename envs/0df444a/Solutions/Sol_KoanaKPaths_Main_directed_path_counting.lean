-- Prove2me | solution 1 for KoanaKPaths.Main.directed_path_counting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:48:15.358406+00:00
-- url     : https://prove2.me/submissions/ab4820a9-ba77-46e5-bea6-bee5e977552e

import Theorems.Thm_KoanaKPaths_Main_amplified_estimator_accuracy
import Theorems.Thm_KoanaKPaths_Main_graph_estimator_machine

set_option synthInstance.maxSize 4096
open scoped BigOperators Classical
namespace KoanaKPaths.Main.TapeSampling

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by simp [uniformMean]

lemma mean_equiv {Ω A : Type} [Fintype Ω] [Fintype A] (e : Ω ≃ A) (f : A → ℝ) :
    uniformMean (fun w => f (e w)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp,Fintype.card_congr e]

lemma mean_prod {Ω A : Type} [Fintype Ω] [Fintype A] (f : Ω × A → ℝ) :
    uniformMean f = uniformMean (fun w : Ω => uniformMean (fun a : A => f (w,a))) := by
  simp only [uniformMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← Finset.sum_div]
  ring

lemma mean_reseed {Ω A : Type} [Fintype Ω] [Fintype A] [Nonempty A]
    (read : Ω → A) (write : Ω → A → Ω)
    (hr : ∀ w a, read (write w a) = a)
    (hw : ∀ w a b, write (write w a) b = write w b)
    (ho : ∀ w, write w (read w) = w) (f : Ω → ℝ) :
    uniformMean f = uniformMean (fun w : Ω => uniformMean (fun a : A => f (write w a))) := by
  let swap : Ω × A → Ω × A := fun z => (write z.1 z.2,read z.1)
  have hi : Function.Involutive swap := by
    intro z
    apply Prod.ext
    · change write (write z.1 z.2) (read z.1) = z.1
      rw [hw,ho]
    · exact hr _ _
  let e : Ω × A ≃ Ω × A := ⟨swap,swap,hi,hi⟩
  calc
    uniformMean f = uniformMean (fun z : Ω × A => f z.1) := by
      rw [mean_prod]
      simp only [mean_const]
    _ = uniformMean (fun z : Ω × A => f (write z.1 z.2)) :=
      (mean_equiv e (fun z => f z.1)).symm
    _ = _ := mean_prod _

lemma mean_prefix {S T : ℕ} (hST : S ≤ T) (f : (Fin S → Bool) → ℝ) :
    uniformMean (fun w : Fin T → Bool => f (fun j => w ⟨j.val,lt_of_lt_of_le j.isLt hST⟩)) =
      uniformMean f := by
  let read (w : Fin T → Bool) : Fin S → Bool := fun j => w ⟨j.val,lt_of_lt_of_le j.isLt hST⟩
  let write (w : Fin T → Bool) (a : Fin S → Bool) : Fin T → Bool :=
    fun j => if h : j.val < S then a ⟨j.val,h⟩ else w j
  have hr (w : Fin T → Bool) (a : Fin S → Bool) : read (write w a) = a := by
    funext j
    simp only [read,write,dif_pos j.isLt]
  have hw (w : Fin T → Bool) (a b : Fin S → Bool) : write (write w a) b = write w b := by
    funext j
    by_cases h : j.val < S <;> simp [write,h]
  have ho (w : Fin T → Bool) : write w (read w) = w := by
    funext j
    by_cases h : j.val < S <;> simp [write,read,h]
  change uniformMean (fun w => f (read w)) = _
  rw [mean_reseed read write hr hw ho]
  simp_rw [hr,mean_const]

lemma tapeSamples_mean (n k a b T : ℕ) (hT : sampleBits n k a b ≤ T)
    (f : (Fin (2*b+1) → Fin (groupTrials k a) → Labels n k × SketchSigns n k k) → ℝ) :
    uniformMean (fun w : Fin T → Bool => tapeSamples n k a b (HypergraphUnreliability.FPRAS.tapeList w) |> f) =
      uniformMean f := by
  have he (w : Fin T → Bool) : tapeSamples n k a b (HypergraphUnreliability.FPRAS.tapeList w) =
      samplesEquiv n k a b (fun j => w ⟨j.val,lt_of_lt_of_le j.isLt hT⟩) := by
    unfold tapeSamples HypergraphUnreliability.FPRAS.tapeList
    congr 1
    funext j
    simp [List.getD_eq_getElem?_getD,lt_of_lt_of_le j.isLt hT]
  simp_rw [he]
  rw [mean_prefix hT (fun bits => f (samplesEquiv n k a b bits))]
  exact mean_equiv (samplesEquiv n k a b) f

lemma fairProb_eq_mean (T : ℕ) (P : (Fin T → Bool) → Prop) :
    HypergraphUnreliability.FPRAS.fairProb T P =
      uniformMean (fun w => if P w then (1 : ℝ) else 0) := by
  simp [HypergraphUnreliability.FPRAS.fairProb,uniformMean,Finset.sum_boole]

end KoanaKPaths.Main.TapeSampling

namespace KoanaKPaths.Main

lemma inv_le_two_pow_ctrl (x : ℝ) (hx : 0 < x) : x⁻¹ ≤ (2 : ℝ)^(ctrl x) := by
  have hl : Real.logb 2 x⁻¹ ≤ (ctrl x : ℝ) := Nat.le_ceil _
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hx)).mp hl
  simpa only [Real.rpow_natCast] using h

lemma control_failure_bound (x : ℝ) (hx : 0 < x) : (2 : ℝ)⁻¹^(ctrl x) ≤ x := by
  have h := inv_anti₀ (inv_pos.mpr hx) (inv_le_two_pow_ctrl x hx)
  simpa only [inv_inv,inv_pow] using h

lemma control_accuracy_bound (x : ℝ) (hx : 0 < x) : 1 ≤ (4 : ℝ)^(ctrl x)*x^2 := by
  have h := inv_le_two_pow_ctrl x hx
  have hh : (1 : ℝ)/x ≤ (2 : ℝ)^(ctrl x) := by simpa only [one_div] using h
  have hm : 1 ≤ (2 : ℝ)^(ctrl x)*x := (div_le_iff₀ hx).mp hh
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 2
  have he : ((2 : ℝ)^(ctrl x))^2 = (4 : ℝ)^(ctrl x) := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  simpa only [one_pow,mul_pow,he] using hs

lemma ctrl_pos (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : 1 ≤ ctrl x := by
  have hlog : 0 < Real.logb 2 x⁻¹ := (Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hx)).mpr (one_lt_inv₀ hx |>.mpr hx1)
  have h : 0 < (ctrl x : ℝ) := lt_of_lt_of_le hlog (Nat.le_ceil _)
  exact_mod_cast h

lemma exp_two_le_sixteen : Real.exp 2 ≤ 16 := by
  have h := Real.exp_one_lt_three
  have hp := Real.exp_pos 1
  rw [show (2 : ℝ) = 1+1 by norm_num,Real.exp_add]
  nlinarith

lemma controlled_group_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    (Real.exp 2*(k : ℝ)^3) / ((1024*(k : ℝ)^3*4^(ctrl ε))*ε^2) ≤ 1/16 := by
  have hacc := control_accuracy_bound ε hε
  have hk0 : 0 < (k : ℝ)^3 := by positivity
  have he := exp_two_le_sixteen
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1024*(k : ℝ)^3*4^(ctrl ε))*ε^2)).mpr
  have hh := mul_le_mul_of_nonneg_left hacc (le_of_lt hk0)
  nlinarith

end KoanaKPaths.Main

set_option synthInstance.maxSize 4096
open scoped BigOperators Classical
open HypergraphUnreliability.FPRAS
namespace KoanaKPaths.Main.Root
open TapeSampling

lemma walkTensor_zeroOne (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) :
    IsZeroOneTensor (walkTensor n arcs k) := by
  intro τ
  unfold walkTensor
  split_ifs <;> simp

lemma walkTensor_count (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) :
    tensorN (walkTensor n arcs k) = (PathCount2k.N n arcs.toFinset k : ℤ) := by
  simp [tensorN,walkTensor,PathCount2k.N,PathCount2k.paths,Finset.filter_filter]

lemma empty_graph_count (arcs : List (Fin 0 × Fin 0)) (k : ℕ) (hk : 1 ≤ k) :
    PathCount2k.N 0 arcs.toFinset k = 0 := by
  haveI : IsEmpty (Fin k → Fin 0) := ⟨fun f => Fin.elim0 (f ⟨0,by omega⟩)⟩
  simp [PathCount2k.N,PathCount2k.paths]

lemma tapeEstimate_den_pos (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) (hk : 1 ≤ k)
    (a b : ℕ) (tape : List Bool) : 0 < (tapeEstimate n arcs k a b tape).den := by
  unfold tapeEstimate
  split_ifs
  · norm_num
  · simp only [estimateFraction,groupTrials,trialDenominator]
    positivity

lemma fairProb_mono (T : ℕ) (P Q : (Fin T → Bool) → Prop) (h : ∀ w, P w → Q w) :
    fairProb T P ≤ fairProb T Q := by
  unfold fairProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,h w (Finset.mem_filter.mp hw).2⟩

lemma tape_accuracy (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) (hk : 1 ≤ k)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (T : ℕ)
    (hT : sampleBits n k (ctrl ε) (ctrl δ) ≤ T) :
    1-δ ≤ fairProb T (fun w =>
      |(((tapeEstimate n arcs k (ctrl ε) (ctrl δ) (tapeList w)).val : ℚ) : ℝ)-
        (PathCount2k.N n arcs.toFinset k : ℝ)| ≤ ε*(PathCount2k.N n arcs.toFinset k : ℝ)) := by
  by_cases hn0 : n=0
  · subst n
    have hc := empty_graph_count arcs k hk
    have he (w : Fin T → Bool) : tapeEstimate 0 arcs k (ctrl ε) (ctrl δ) (tapeList w) = ⟨0,1⟩ := by
      simp [tapeEstimate]
    simp only [he,Frac.val,hc,Nat.cast_zero,Rat.cast_zero,Rat.cast_div,Rat.cast_one,
      Nat.cast_one,zero_div,sub_zero,abs_zero,mul_zero,le_refl]
    have hp : (2 : ℝ)^T ≠ 0 := by positivity
    simp only [fairProb,Finset.filter_true,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
      Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,div_self hp]
    linarith
  · have hs := amplified_estimator_accuracy n k (by omega) hk (walkTensor n arcs k)
      (walkTensor_zeroOne n arcs k) ε δ hε hδ
    have hc : (tensorN (walkTensor n arcs k) : ℝ) = (PathCount2k.N n arcs.toFinset k : ℝ) := by
      rw [walkTensor_count]
      norm_cast
    have he := tapeSamples_mean n k (ctrl ε) (ctrl δ) T hT
      (fun z => if |(((estimateFraction (walkTensor n arcs k) (ctrl ε) (ctrl δ) z).val : ℚ) : ℝ)-
        (PathCount2k.N n arcs.toFinset k : ℝ)| ≤ ε*(PathCount2k.N n arcs.toFinset k : ℝ)
        then (1 : ℝ) else 0)
    rw [fairProb_eq_mean]
    simp only [tapeEstimate,if_neg hn0]
    rw [he]
    simpa only [hc] using hs

end KoanaKPaths.Main.Root

open KoanaKPaths.Main
theorem solution :
    ∃ (M : CoinMachine) (K c : ℕ), ∀ (n : ℕ) (arcs : List (Fin n × Fin n)), arcs.Nodup →
      (∀ p ∈ arcs, p.1 ≠ p.2) → ∀ k : ℕ, 1 ≤ k →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ T : ℕ, timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ) < T →
        (∀ ω : Fin T → Bool, ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (graphInput n arcs k ε δ) (tapeList ω)
            (timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ))
            (fracCode Nhat)) ∧
        1 - δ ≤ fairProb T (fun ω => ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (graphInput n arcs k ε δ) (tapeList ω)
            (timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ))
            (fracCode Nhat) ∧
          |((Nhat.val : ℚ) : ℝ) - (PathCount2k.N n arcs.toFinset k : ℝ)| ≤
            ε * (PathCount2k.N n arcs.toFinset k : ℝ)) := by
  classical
  obtain ⟨M,K,c,hM⟩ := KoanaKPaths.Main.graph_estimator_machine
  refine ⟨M,K,c,?_⟩
  intro n arcs hdup hloop k hk ε δ hε hε1 hδ hδ1 T hT
  have h := hM n arcs hdup hloop k hk (ctrl ε) (ctrl δ)
    (KoanaKPaths.Main.ctrl_pos ε hε hε1) (KoanaKPaths.Main.ctrl_pos δ hδ hδ1)
  have hbits : sampleBits n k (ctrl ε) (ctrl δ) ≤ T := le_trans h.1 hT.le
  have hr (w : Fin T → Bool) :
      M.RunsWithin (graphInput n arcs k ε δ) (tapeList w)
        (timeBudget K c k (n+(graphCode n arcs).length) (ctrl ε) (ctrl δ))
        (fracCode (tapeEstimate n arcs k (ctrl ε) (ctrl δ) (tapeList w))) := by
    apply h.2
    simpa only [tapeList,List.length_ofFn] using hT
  constructor
  · intro w
    exact ⟨_,Root.tapeEstimate_den_pos n arcs k hk _ _ _,hr w⟩
  · apply le_trans (Root.tape_accuracy n arcs k hk ε δ hε hδ T hbits)
    apply Root.fairProb_mono
    intro w hw
    exact ⟨_,Root.tapeEstimate_den_pos n arcs k hk _ _ _,hr w,hw⟩
