-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.select_block
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:50:11.700995+00:00
-- url     : https://prove2.me/submissions/68bdb48a-6243-4b85-ac70-f49116fde22c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/BlockSelection.lean:L90-L168
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.select_block. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_small_dyadic_difference
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_gradEnergy_le_cost
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_gradEnergy_midpoint

-- ---- from OAI.Analysis.LipschitzEquivalence.HilbertBlocks ----
namespace OAI

universe uE uF uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

variable {E : Type uE} [AddCommGroup E] [Module ℝ E]

variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

theorem map_dyadicMean (T : E →ₗ[ℝ] F) (u : ℕ → E) (n k : ℕ) :
    T (dyadicMean u n k) = dyadicMean (fun i => T (u i)) n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [dyadicMean_succ, map_smul, map_add, ih]

theorem dyadicMean_le (u : ℕ → ℝ) (n k : ℕ) {b : ℝ}
    (h : ∀ i, k ≤ i → i < k+2^n → u i ≤ b) : dyadicMean u n k ≤ b := by
  induction n generalizing k with
  | zero => exact h k le_rfl (by simp)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ : dyadicMean u n k ≤ b := ih k (fun i hi hi' => h i hi (by omega))
    have h₂ : dyadicMean u n (k+2^n) ≤ b :=
      ih (k+2^n) (fun i hi hi' => h i (by omega) (by omega))
    simp only [dyadicMean_succ, smul_eq_mul]
    linarith

theorem le_dyadicMean (u : ℕ → ℝ) (n k : ℕ) {b : ℝ}
    (h : ∀ i, k ≤ i → i < k+2^n → b ≤ u i) : b ≤ dyadicMean u n k := by
  induction n generalizing k with
  | zero => exact h k le_rfl (by simp)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ : b ≤ dyadicMean u n k := ih k (fun i hi hi' => h i hi (by omega))
    have h₂ : b ≤ dyadicMean u n (k+2^n) :=
      ih (k+2^n) (fun i hi hi' => h i (by omega) (by omega))
    simp only [dyadicMean_succ, smul_eq_mul]
    linarith

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.FiniteRows ----
namespace OAI

universe uA uB

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

namespace RowFamily
variable {A : Type uA} {B : Type uB}

theorem rich_monochromatic [Fintype B] [Nonempty B] (R : RowFamily A) (hR : R.Rich)
    (c : A → B) : ∃ b, (R.restrict (fun a => c a = b)).Rich := by
  classical
  by_contra! h
  have hh : ∀ b : B, ∃ n, ∀ v : Fin n → A, ¬ (R.accepts v ∧ ∀ i, c (v i) = b) := by
    intro b
    simpa only [Rich,restrict,not_forall,not_exists] using h b
  choose N hN using hh
  let k := Finset.univ.sup N
  let m := Fintype.card B*(k+1)
  obtain ⟨v,hv⟩ := hR m
  obtain ⟨b,_,hb⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := Finset.univ) (t := (Finset.univ : Finset B)) (f := fun i : Fin m => c (v i))
    (n := k+1) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by simp [m])
  let s : Finset (Fin m) := Finset.univ.filter (fun i => c (v i) = b)
  have hNb : N b ≤ k := Finset.le_sup (f := N) (Finset.mem_univ b)
  have hcard : N b ≤ s.card := by change N b ≤ (Finset.univ.filter _).card; omega
  let e : Fin (N b) ↪o Fin m :=
    (Fin.castLEOrderEmb hcard).trans (s.orderEmbOfFin rfl)
  apply hN b (v ∘ e)
  refine ⟨R.hereditary e v hv,?_⟩
  intro i
  have hi : e i ∈ s := by
    exact s.orderEmbOfFin_mem rfl _
  exact (Finset.mem_filter.mp hi).2

theorem rich_finite_cover [Fintype B] [Nonempty B] (R : RowFamily A) (hR : R.Rich)
    (P : B → A → Prop) (hP : ∀ a : A, ∃ b, P b a) :
    ∃ b, (R.restrict (P b)).Rich := by
  classical
  choose c hc using hP
  obtain ⟨b,hb⟩ := R.rich_monochromatic hR c
  refine ⟨b,fun n => ?_⟩
  obtain ⟨v,hv,hc'⟩ := hb n
  exact ⟨v,hv,fun i => by simpa only [hc' i] using hc (v i)⟩

end RowFamily
end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothCalculus ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

namespace Smooth

end Smooth

open FreeSpace

theorem gradEnergy_nonneg (a : MolecularData H) (f : Smooth H) : 0 ≤ gradEnergy a f := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.EnergyEstimates ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem gradEnergy_smul (a : MolecularData H) (c : ℝ) (f : Smooth H) :
    gradEnergy a (c • f) = c^2*gradEnergy a f := by
  simp only [gradEnergy,map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp only [intervalIntegral.integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem augmentedEnergy_nonneg (a : MolecularData H) (S : Finset H) (D : ℝ) (f : Smooth H) :
    0 ≤ augmentedEnergy a S D f :=
  add_nonneg (gradEnergy_nonneg _ _)
    (Finset.sum_nonneg (fun point _ => sq_nonneg (D * f.val point)))

theorem augmentedEnergy_midpoint (a : MolecularData H) (S : Finset H) (D : ℝ)
    (f g : Smooth H) :
    augmentedEnergy a S D ((1/2:ℝ) • (f+g)) =
      (augmentedEnergy a S D f+augmentedEnergy a S D g)/2-augmentedEnergy a S D (f-g)/4 := by
  have he (p : H) : (D*((((1/2:ℝ) • (f+g)) : Smooth H).val p))^2 =
      ((D*f.val p)^2+(D*g.val p)^2)/2-(D*((f-g).val p))^2/4 := by
    change (D*((1/2:ℝ)*(f.val p+g.val p)))^2 =
      ((D*f.val p)^2+(D*g.val p)^2)/2-(D*(f.val p-g.val p))^2/4
    ring
  simp only [augmentedEnergy,gradEnergy_midpoint,he,Finset.sum_sub_distrib,
    ← Finset.sum_div,Finset.sum_add_distrib]
  ring

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.BlockSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem half_sum_lipschitz {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p+g p)/2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hf' := hf.dist_le_mul p q
  have hg' := hg.dist_le_mul p q
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at *
  have he : (f p+g p)/2-(f q+g q)/2 = ((f p-f q)+(g p-g q))/2 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have := abs_add_le (f p-f q) (g p-g q)
  linarith

theorem half_sub_lipschitz {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p-g p)/2) := by
  simpa only [sub_eq_add_neg,Pi.neg_apply] using half_sum_lipschitz hf hg.neg

theorem dyadicMean_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (dyadicMean u n k).val := by
  induction n generalizing k with
  | zero => exact hu k
  | succ n ih =>
    convert half_sum_lipschitz (ih k) (ih (k+2^n)) using 1
    ext p
    change (1/2:ℝ)*((dyadicMean u n k).val p+(dyadicMean u n (k+2^n)).val p) = _
    ring

theorem dyadicMean_zero_value {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (dyadicMean u n k).val 0 = 0 := by
  have he := map_dyadicMean (Smooth.eval (0:H)) u n k
  change (dyadicMean u n k).val 0 = dyadicMean (fun i => (u i).val 0) n k at he
  rw [he]
  exact le_antisymm (dyadicMean_le _ _ _ (fun i _ _ => (hu i).le))
    (le_dyadicMean _ _ _ (fun i _ _ => (hu i).ge))

theorem halfBlock_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (halfBlock u n k).val := by
  convert half_sub_lipschitz (dyadicMean_lipschitz u hu n k) (dyadicMean_lipschitz u hu n (k+2^n)) using 1
  ext p
  change (1/2:ℝ)*((dyadicMean u n k).val p-(dyadicMean u n (k+2^n)).val p) = _
  ring

theorem halfBlock_zero_value (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (halfBlock u n k).val 0 = 0 := by
  change (1/2:ℝ)*((dyadicMean u n k).val 0-(dyadicMean u n (k+2^n)).val 0) = 0
  rw [dyadicMean_zero_value u hu,dyadicMean_zero_value u hu,sub_self,mul_zero]

theorem augmentedEnergy_smul (a : MolecularData H) (S : Finset H) (D c : ℝ) (f : Smooth H) :
    augmentedEnergy a S D (c • f) = c^2*augmentedEnergy a S D f := by
  simp only [augmentedEnergy,gradEnergy_smul,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  change (D*(c*f.val p))^2 = c^2*(D*f.val p)^2
  ring

theorem one_augmentedEnergy_le {K : Set H} {C ρ : ℝ} {μ : ℕ → Space H}
    (a b : RowItem K C ρ μ) (S : Finset H) :
    augmentedEnergy a.a S 1 b.f ≤ C+∑ p ∈ S, ‖p‖^2 := by
  apply add_le_add ((gradEnergy_le_cost a.a b.f b.lip).trans a.cost_le)
  apply Finset.sum_le_sum
  intro p _
  have hp : |b.f.val p| ≤ ‖p‖ := by
    have h := b.lip.dist_le_mul p 0
    simpa only [Real.dist_eq,b.zero,sub_zero,NNReal.coe_one,one_mul,dist_zero_right,Real.norm_eq_abs] using h
  change (1*b.f.val p)^2 ≤ ‖p‖^2
  simpa only [one_mul,sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hp

theorem select_block {K : Set H} {C ρ α : ℝ} {μ : ℕ → Space H}
    (hα : 0 < α) (P : RowItem K C ρ μ → Prop)
    (hRich : ((triangularRows K C ρ α μ).restrict P).Rich)
    (S : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (z : Smooth H) (a : RowItem K C ρ μ), LipschitzWith 1 z.val ∧ z.val 0 = 0 ∧
      P a ∧ α ≤ smoothPair a.a z ∧
      ((triangularRows K C ρ α μ).restrict
        (fun b => P b ∧ augmentedEnergy b.a S 1 z < ε)).Rich := by
  classical
  let B : ℝ := C+∑ p ∈ S, ‖p‖^2
  obtain ⟨d0,hd0⟩ := exists_nat_gt (4*B/ε)
  let d := d0+1
  have hd : 4*B < (d : ℝ)*ε := by
    have : (4*B/ε) < (d : ℝ) := hd0.trans (by simp [d])
    exact (div_lt_iff₀ hε).mp this
  have hdpos : 0 < d := by omega
  let : NeZero d := ⟨by omega⟩
  have hpow : 0 < (2:ℕ)^d := pow_pos (by norm_num) d
  let : NeZero (2^d) := ⟨by omega⟩
  obtain ⟨row,hrow,hP⟩ := hRich (2^d)
  let u : ℕ → Smooth H := fun k => if hk : k < 2^d then (row ⟨k,hk⟩).f else 0
  have hu (k : ℕ) (hk : k < 2^d) : u k = (row ⟨k,hk⟩).f := dite_eq_left hk
  have huLip (k : ℕ) : LipschitzWith 1 (u k).val := by
    by_cases hk : k < 2^d
    · rw [hu k hk]; exact (row ⟨k,hk⟩).lip
    · simp only [u,dite_eq_right hk]
      exact (LipschitzWith.const (0:ℝ)).weaken (by norm_num)
  have hu0 (k : ℕ) : (u k).val 0 = 0 := by
    by_cases hk : k < 2^d
    · rw [hu k hk]; exact (row ⟨k,hk⟩).zero
    · simp [u,hk]
  let colorP : (Fin d × Fin (2^d)) → RowItem K C ρ μ → Prop := fun c b =>
    c.2.val+2^(c.1.val+1) ≤ 2^d ∧
      augmentedEnergy b.a S 1 (dyadicMean u c.1.val c.2.val-
        dyadicMean u c.1.val (c.2.val+2^c.1.val)) < ε
  have hcover (b : RowItem K C ρ μ) : ∃ c, colorP c b := by
    obtain ⟨n,k,hn,hk,hsmall⟩ := exists_small_dyadic_difference
      (augmentedEnergy b.a S 1) (augmentedEnergy_nonneg b.a S 1)
      (augmentedEnergy_midpoint b.a S 1) u hε d hd (fun k hk => by
        rw [hu k hk]; exact one_augmentedEnergy_le b (row ⟨k,hk⟩) S)
    have hkp : k < 2^d := by have := pow_pos (by norm_num : 0<2) (n+1); omega
    exact ⟨(⟨n,hn⟩,⟨k,hkp⟩),hk,hsmall⟩
  obtain ⟨c,hc⟩ := RowFamily.rich_finite_cover _ hRich colorP hcover
  obtain ⟨one,hone⟩ := hc 1
  have hbound : c.2.val+2^(c.1.val+1) ≤ 2^d := (hone.2 0).1
  let n := c.1.val
  let k := c.2.val
  have hsplit : (2:ℕ)^(n+1) = 2^n+2^n := by omega
  have hp : 0 < (2:ℕ)^n := pow_pos (by norm_num) n
  let mid : Fin (2^d) := ⟨k+2^n-1,by dsimp [k,n] at *; omega⟩
  let z := halfBlock u n k
  have hhigh : 4*α ≤ smoothPair (row mid).a (dyadicMean u n k) := by
    rw [map_dyadicMean]
    apply le_dyadicMean
    intro i hi hi'
    have hiN : i < 2^d := by dsimp [k,n] at *; omega
    rw [hu i hiN]
    exact hrow.1 mid ⟨i,hiN⟩ (by change i ≤ mid.val; dsimp [mid]; omega)
  have hlow : smoothPair (row mid).a (dyadicMean u n (k+2^n)) ≤ α := by
    rw [map_dyadicMean]
    apply dyadicMean_le
    intro i hi hi'
    have hiN : i < 2^d := by dsimp [k,n] at *; omega
    rw [hu i hiN]
    exact (le_abs_self _).trans (hrow.2 mid ⟨i,hiN⟩ (by change mid.val < i; dsimp [mid]; omega))
  have hzpair : α ≤ smoothPair (row mid).a z := by
    simp only [z,halfBlock,map_smul,map_sub,smul_eq_mul]
    linarith
  refine ⟨z,row mid,halfBlock_lipschitz u huLip n k,halfBlock_zero_value u hu0 n k,hP mid,hzpair,?_⟩
  intro N
  obtain ⟨v,hv,hcolor⟩ := hc N
  refine ⟨v,hv.1,fun i => ⟨hv.2 i,?_⟩⟩
  have he := (hcolor i).2
  have hnonneg := augmentedEnergy_nonneg (v i).a S 1
    (dyadicMean u n k-dyadicMean u n (k+2^n))
  change augmentedEnergy (v i).a S 1 ((1/2:ℝ) • _) < ε
  rw [augmentedEnergy_smul]
  change augmentedEnergy (v i).a S 1 (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε at he
  nlinarith

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.select_block.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.select_block.{uH}
