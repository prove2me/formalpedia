-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.exists_finite_source_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:42:39.915989+00:00
-- url     : https://prove2.me/submissions/be785827-5f07-4c9f-9447-1455cdf21573

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteSourceFamily.lean:L17-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.exists_finite_source_family. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Theorems.Thm_OAI_TreeEdit_BinaryLower_EditStep_common_subsequence
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteAlphabet_finite_tree_alphabet_bounds
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_half_children
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_root_mean_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_separation_of_half_children
import Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_exists_word_image_lower_of_root_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSupply_finite_tree_odd_prime_family
import Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_lower_bound

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation ----
namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- Positive prime entries make every cyclic leaf period positive. -/
theorem wordPeriods_pos {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) (l : Leaf m k) : 0 < wordPeriods primes l := by
  unfold wordPeriods FiniteVectors.leafPeriod
  exact Nat.mul_pos (by decide) (Finset.prod_pos fun j _ => hpos j _)

/-- The concrete parameter group is finite, not merely a formal product. -/
theorem finite_wordState {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) : Finite (State (wordPeriods primes)) := by
  let (l : Leaf m k) : NeZero (wordPeriods primes l) :=
    ⟨Nat.ne_of_gt (wordPeriods_pos primes hpos l)⟩
  infer_instance

/-- The actual tagged cyclic-state alphabet is finite. -/
theorem finite_wordSymbol {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (hpos : ∀ j i, 0 < primes j i) : Finite (Symbol (wordPeriods primes)) := by
  let (l : Leaf m k) : NeZero (wordPeriods primes l) :=
    ⟨Nat.ne_of_gt (wordPeriods_pos primes hpos l)⟩
  infer_instance

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSeparation ----
namespace OAI

/-!
# Geometric separation for the concrete finite tree

The prime construction supplies the half-child condition in the
geometric induction.
-/

noncomputable section
namespace TreeEdit.BinaryLower.FiniteTree

open scoped BigOperators

/-- Source finite-tree separation for the actual prime periods and words. -/
theorem finiteWord_separation {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (h : ℕ) (p : List (Fin (20 * k))) (hlen : p.length + h = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    (((20 * k * k ^ (20 * k)) ^ h : ℕ) : ℝ) / (4 : ℝ) ^ h ≤
      (deficit ((20 * k * k ^ (20 * k)) ^ h)
        (finiteWord primes i₀ (k ^ (20 * k)) h p x)
        (finiteWord primes i₀ (k ^ (20 * k)) h p
          (x + t • wordW primes i₀ p)) : ℝ) := by
  apply finiteWord_separation_of_half_children primes i₀ (by omega)
    (pow_pos (by omega) _) _ h p hlen x t ht
  intro p hp a b t ht
  exact finiteWord_half_children hk primes i₀ p hp hinj hprime hlarge a b t ht

/-- Distinct large primes give the uniform root deficit for the
prescribed half-period shift. -/
theorem finiteWord_root_deficit {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (x : State (wordPeriods primes)) :
    (((20 * k * k ^ (20 * k)) ^ k : ℕ) : ℝ) / (4 : ℝ) ^ k ≤
      (deficit ((20 * k * k ^ (20 * k)) ^ k)
        (finiteWord primes i₀ (k ^ (20 * k)) k [] x)
        (finiteWord primes i₀ (k ^ (20 * k)) k []
          (x + wordW primes i₀ [])) : ℝ) := by
  have h := finiteWord_separation hk primes i₀ hinj hprime hlarge k []
    (by simp) x 1 (by simp)
  simpa using h

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteNumeric ----
namespace OAI

/-!
# Arithmetic for the finite-tree obstruction

The parameter estimate and final rearrangement in `prop:finite-lower` hold
with the explicit absolute constant 34.
-/

namespace TreeEdit.BinaryLower.FiniteNumeric

lemma period_ratio_bound {k : ℕ} (hk : 1 ≤ k) :
    2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k)
      ≤ 8 / (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) ^ (10 * k) := pow_pos hk0 _
  have hb : 0 < (k : ℝ) ^ k := pow_pos hk0 _
  have hp : (k : ℝ) * (k : ℝ) ^ k ≤ (k : ℝ) ^ (10 * k) := by
    calc
      (k : ℝ) * (k : ℝ) ^ k = (k : ℝ) ^ (k + 1) := by ring
      _ ≤ (k : ℝ) ^ (10 * k) :=
        pow_le_pow_right₀ hk1 (by omega)
  have ht : (k : ℝ) ^ (20 * k) = ((k : ℝ) ^ (10 * k)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [ht]
  have hs : 2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) /
      ((k : ℝ) ^ (10 * k)) ^ 2 = 8 * (k : ℝ) / (k : ℝ) ^ (10 * k) := by
    field_simp
    ring
  rw [hs]
  apply (div_le_div_iff₀ ha hb).2
  nlinarith

/-- The final line of `eq:finite-root-upper`, with an explicit constant. -/
theorem finite_root_bound {k : ℕ} {M V : ℝ} (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hV : V ≤ 4 * M *
      (2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k) +
        1 / (2 * (k : ℝ) ^ k))) :
    V ≤ 34 * M / (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : (k : ℝ) ^ k ≠ 0 := ne_of_gt (pow_pos hk0 _)
  calc
    V ≤ 4 * M *
      (2 * (k : ℝ) * (4 * (k : ℝ) ^ (10 * k)) / (k : ℝ) ^ (20 * k) +
        1 / (2 * (k : ℝ) ^ k)) := hV
    _ ≤ 4 * M * (8 / (k : ℝ) ^ k + 1 / (2 * (k : ℝ) ^ k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [period_ratio_bound hk]
    _ = 34 * M / (k : ℝ) ^ k := by field_simp; ring

/-- The source averaging length `J=4k^(10k)` lies within the row budget
`T=k^(20k)` already for every `k≥2`. -/
theorem averaging_length_le_rows {k : ℕ} (hk : 2 ≤ k) :
    4 * k ^ (10 * k) ≤ k ^ (20 * k) := by
  have hfour : 4 ≤ k ^ (10 * k) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
      _ ≤ k ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    4 * k ^ (10 * k) ≤ k ^ (10 * k) * k ^ (10 * k) :=
      Nat.mul_le_mul_right _ hfour
    _ = k ^ (20 * k) := by rw [← pow_add]; congr 1; omega

end TreeEdit.BinaryLower.FiniteNumeric

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteL1Tree ----
namespace OAI

/-!
# Actual ℓ₁ maps and the finite-tree obstruction

The finite-group displacement identity yields the finite-tree root estimate
from geometric bounds on the concrete translations.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical
open scoped BigOperators

/-- Parameter normalization gives the root estimate with the absolute
constant 34. -/
theorem source_mean_bound34 {A : Type*} [AddCommGroup A] [Fintype A]
    (F : A → RealL1) (root : A) {k : ℕ} {M : ℝ}
    (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hroot : (𝔼 x : A, ‖F (x + root) - F x‖) ≤
      4 * ((k : ℝ) * ((2 * (4 * (k : ℝ) ^ (10 * k)) /
        (k : ℝ) ^ (20 * k)) * M) + M / (2 * (k : ℝ) ^ k))) :
    (𝔼 x : A, ‖F (x + root) - F x‖) ≤ 34 * M / (k : ℝ) ^ k := by
  apply TreeEdit.BinaryLower.FiniteNumeric.finite_root_bound hk hM
  convert hroot using 1
  ring

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteWordL1Mean ----
namespace OAI

/-!
# The actual finite word's averaged ℓ₁ displacement

This specializes the proved finite-group Fourier obstruction to the concrete
cyclic parameter space and recursive word evaluator. The only metric input is
that the chosen map into actual ℓ₁ does not expand ordinary edit distance.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

open Classical
open scoped BigOperators

/-- The source parameter choice gives the explicit `34 M/k^k` averaged
root bound for every nonexpanding map of the actual constructed word image. -/
theorem finiteWord_root_mean_bound34 {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (hk : 2 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    [Fintype (State (wordPeriods p))]
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ (k ^ (20 * k)) k [] x)
        (finiteWord p i₀ (k ^ (20 * k)) k [] y) : ℝ)) :
    (𝔼 x : State (wordPeriods p), ‖F (x + wordW p i₀ []) - F x‖) ≤
      34 * ((m * k ^ (20 * k) : ℕ) : ℝ) ^ k / (k : ℝ) ^ k := by
  apply FiniteActivity.source_mean_bound34 F (wordW p i₀ []) (by omega) (by positivity)
  have hroot := finiteWord_root_mean_bound p i₀ (by omega) hppos hp
    (k ^ (20 * k)) (by positivity) (FiniteNumeric.averaging_length_le_rows hk) F hF
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hroot

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteAlphabet ----
namespace OAI

namespace TreeEdit.BinaryLower.FiniteAlphabet

open scoped BigOperators

/-- Bounding each factor bounds the leaf period from the manuscript. -/
theorem leaf_period_le {m k : ℕ} (p : Fin k → Fin m → ℕ)
    (hupper : ∀ q i, p q i ≤ k ^ 5) (a : Fin k → Fin m) :
    2 * (∏ q, p q (a q)) ≤ 2 * k ^ (5 * k) := by
  apply Nat.mul_le_mul_left
  calc
    (∏ q, p q (a q)) ≤ ∏ _q : Fin k, k ^ 5 :=
      Finset.prod_le_prod' fun q _ => hupper q (a q)
    _ = k ^ (5 * k) := by simp [← pow_mul]

/-- Positivity of every factor makes every leaf modulus nonzero. -/
theorem leaf_period_pos {m k : ℕ} (p : Fin k → Fin m → ℕ)
    (hpos : ∀ q i, 0 < p q i) (a : Fin k → Fin m) :
    0 < 2 * (∏ q, p q (a q)) := by
  apply Nat.mul_pos (by decide)
  exact Finset.prod_pos fun q _ => hpos q (a q)

/-- Specialization to the source's products of one prime from each depth.
Only positivity and the upper prime-size bound are needed for cardinality. -/
theorem prime_product_alphabet_bounds {k : ℕ} (hk : 2 ≤ k)
    (p : Fin k → Fin (20 * k) → ℕ)
    (hpos : ∀ q i, 0 < p q i) (hupper : ∀ q i, p q i ≤ k ^ 5) :
    let Q : Word (Fin (20 * k)) k → ℕ := fun a =>
      2 * ∏ q, p q ((Equiv.vectorEquivFin (Fin (20 * k)) k a) q)
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by
  apply finite_tree_alphabet_bounds hk
  · intro a
    exact leaf_period_pos p hpos _
  · intro a
    exact leaf_period_le p hupper _

end TreeEdit.BinaryLower.FiniteAlphabet

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SubsequenceIntersection ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Composing two common-subsequence loss bounds adds their costs. -/
theorem common_subsequence_compose {α : Type*} {x y z : List α} {m n : ℕ}
    (hxy : ∃ u : List α, u.Sublist x ∧ u.Sublist y ∧
      x.length + y.length ≤ m + 2 * u.length)
    (hyz : ∃ v : List α, v.Sublist y ∧ v.Sublist z ∧
      y.length + z.length ≤ n + 2 * v.length) :
    ∃ w : List α, w.Sublist x ∧ w.Sublist z ∧
      x.length + z.length ≤ m + n + 2 * w.length := by
  obtain ⟨u, hux, huy, hu⟩ := hxy
  obtain ⟨v, hvy, hvz, hv⟩ := hyz
  obtain ⟨w, hwu, hwv, hw⟩ := common_sublist_lower_bound huy hvy
  exact ⟨w, hwu.trans hux, hwv.trans hvz, by omega⟩

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EditLCSLower ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- A script of cost `n` has a common subsequence with at most `2*n` unmatched
symbols in its two endpoints. Intermediate words are unrestricted. -/
theorem EditScript.common_subsequence {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 * n + 2 * z.length := by
  induction h with
  | nil x =>
      exact ⟨x, List.Sublist.refl _, List.Sublist.refl _, by omega⟩
  | cons hstep hscript ih =>
      obtain ⟨z, hzx, hzy, hlen⟩ :=
        common_subsequence_compose (EditStep.common_subsequence hstep) ih
      exact ⟨z, hzx, hzy, by omega⟩

/-- The insertion/deletion deficit of a script's endpoints is at most twice
its ordinary unit-edit cost. -/
theorem EditScript.lcs_loss_le {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    x.length + y.length - 2 * lcs x y ≤ 2 * n := by
  obtain ⟨z, hzx, hzy, hlen⟩ := EditScript.common_subsequence h
  have hz : z.length ≤ lcs x y := by
    apply le_csSup
    · refine ⟨x.length, ?_⟩
      rintro k ⟨w, hwx, hwy, rfl⟩
      exact hwx.length_le
    · exact ⟨z, hzx, hzy, rfl⟩
  omega

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EditDeficit ----
namespace OAI

/-!
Both metric comparisons in the preliminary section, for the actual unrestricted
unit-cost edit scripts and longest-common-subsequence definitions.
-/
namespace TreeEdit.BinaryLower

/-- Second inequality of source equation `eq:metric-conversion`. -/
theorem delta_le_twice_editDistance {α : Type*} (x y : List α) :
    x.length + y.length - 2 * lcs x y ≤ 2 * ed x y := by
  have hs : EditScript x y (ed x y) :=
    TreeEdit.ed_script x y
  exact EditScript.lcs_loss_le hs

/-- Lower inequality of source equation `eq:deficit`, on equal-length words. -/
theorem deficit_le_editDistance {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y ≤ ed x y := by
  have h := delta_le_twice_editDistance x y
  rw [hx, hy] at h
  unfold deficit
  omega

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSourceFamily ----
namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower

open FiniteTree
open scoped BigOperators

/-- A finite-alphabet family with distortion constant `1/34`, constructed
from finite coordinate groups and their word images. -/
theorem exists_finite_source_family :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  classical
  obtain ⟨K, hK⟩ := PrimeSupply.finite_tree_odd_prime_family
  refine ⟨1 / 34, by norm_num, K, ?_⟩
  intro k hk
  obtain ⟨hk2, primes, hprimes⟩ := hK k hk
  let p : Fin k → Fin (20 * k) → ℕ := fun q i => primes (q, i)
  have hpprime : ∀ q i, Nat.Prime (p q i) := fun q i => (hprimes (q, i)).1
  have hppos : ∀ q i, 0 < p q i := fun q i => (hpprime q i).pos
  have hplarge : ∀ q i, k ^ 4 ≤ p q i := fun q i => (hprimes (q, i)).2.2.1
  have hpupper : ∀ q i, p q i ≤ k ^ 5 := fun q i => (hprimes (q, i)).2.2.2
  have hpinj : Function.Injective (fun z : Fin k × Fin (20 * k) => p z.1 z.2) :=
    primes.injective
  let i₀ : Fin (20 * k) := ⟨0, by omega⟩
  let Γ := Symbol (wordPeriods p)
  let A := State (wordPeriods p)
  let : Finite Γ := finite_wordSymbol p hppos
  let : Fintype Γ := Fintype.ofFinite Γ
  let : Finite A := finite_wordState p hppos
  let : Fintype A := Fintype.ofFinite A
  have hΓ := FiniteAlphabet.prime_product_alphabet_bounds hk2 p hppos hpupper
  change Finite Γ ∧ 1 ≤ Nat.card Γ ∧ Nat.card Γ ≤ finiteSourceLength k at hΓ
  have hΓ1 : 1 ≤ Fintype.card Γ := by simpa only [Nat.card_eq_fintype_card] using hΓ.2.1
  have hΓM : Fintype.card Γ ≤ finiteSourceLength k := by
    simpa only [Nat.card_eq_fintype_card] using hΓ.2.2
  let G : A → Word Γ (finiteSourceLength k) := rootWord p i₀ (k ^ (20 * k))
  let z : A := wordW p i₀ []
  have hMnat : 0 < finiteSourceLength k := by
    unfold finiteSourceLength
    positivity
  have hM : (0 : ℝ) < finiteSourceLength k := by exact_mod_cast hMnat
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsep : ∀ x : A, (finiteSourceLength k : ℝ) / (4 : ℝ) ^ k ≤
      (ed (G x).val (G (x + z)).val : ℝ) := by
    intro x
    have hd := finiteWord_root_deficit hk2 p i₀ hpinj hpprime hplarge x
    have he := deficit_le_editDistance
      (finiteWord_length p i₀ (k ^ (20 * k)) k [] x)
      (finiteWord_length p i₀ (k ^ (20 * k)) k [] (x + z))
    exact hd.trans (Nat.cast_le.mpr he)
  have hmean : ∀ F : A → RealL1,
      (∀ x y, ‖F x - F y‖ ≤ (ed (G x).val (G y).val : ℝ)) →
      (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A ≤
        34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k := by
    intro F hF
    have h := finiteWord_root_mean_bound34 p i₀ hk2 hppos hpupper F hF
    simpa only [Fintype.expect_eq_sum_div_card, finiteSourceLength, Nat.cast_pow] using h
  obtain ⟨W, _, hW, hdist⟩ := ParameterImage.exists_word_image_lower_of_root_bound
    G z ((finiteSourceLength k : ℝ) / (4 : ℝ) ^ k)
    (34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k)
    (by positivity) (by positivity) hsep hmean
  refine ⟨Γ, inferInstance, hΓ1, hΓM, W, hW, ?_⟩
  have hratio : (finiteSourceLength k : ℝ) / (4 : ℝ) ^ k /
      (34 * (finiteSourceLength k : ℝ) / (k : ℝ) ^ k) =
        (1 / 34 : ℝ) * ((k : ℝ) / 4) ^ k := by
    rw [div_pow]
    field_simp
  rw [hratio] at hdist
  exact hdist

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open FiniteTree
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.exists_finite_source_family := @_root_.OAI.TreeEdit.BinaryLower.exists_finite_source_family
