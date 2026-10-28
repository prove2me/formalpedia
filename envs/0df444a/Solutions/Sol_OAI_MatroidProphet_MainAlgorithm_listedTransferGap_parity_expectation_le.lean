-- Prove2me | solution 1 for OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:25.508121+00:00
-- url     : https://prove2.me/submissions/eae51223-9035-4998-b629-cc5e4cada331

import Mathlib
import Definitions.Def_OAIW2MS000

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

noncomputable section

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

end

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Basic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

lemma natRank_mono (M : Matroid α) {X Y : Set α} (h : X ⊆ Y) :
    natRank M X ≤ natRank M Y :=
  ENat.toNat_le_toNat (M.eRk_mono h) (rank_ne_top M Y)

lemma densityExpansion_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P : Set α) : M.IsFlat (densityExpansion M hE κ D P) :=
  (densityExpansion_spec M hE κ D P).1.1

lemma densityExpansion_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) {P P' : Set α} (hPP' : P ⊆ P') :
    densityExpansion M hE κ D P ⊆ densityExpansion M hE κ D P' := by
  let Q := densityExpansion M hE κ D P
  let Q' := densityExpansion M hE κ D P'
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQ' : IsDensityMax M κ D P' Q' := (densityExpansion_spec M hE κ D P').1
  have hPint : P ⊆ Q ∩ Q' := subset_inter hQ.2.1 (hPP'.trans hQ'.2.1)
  have hP'cl : P' ⊆ M.closure (Q ∪ Q') :=
    hQ'.2.1.trans (subset_union_right.trans (M.subset_closure _ (by simp [hE])))
  have hInt := hQ.2.2 (Q ∩ Q') (flat_inter M hQ.1 hQ'.1) hPint
  have hSup := densityObjective_supermod M hE κ D Q Q'
  have hjoin : IsDensityMax M κ D P' (M.closure (Q ∪ Q')) := by
    refine ⟨Matroid.isFlat_closure (M := M) _, hP'cl, ?_⟩
    intro Z hZ hPZ
    have hm := hQ'.2.2 Z hZ hPZ
    omega
  exact (subset_union_left.trans (M.subset_closure _ (by simp [hE]))).trans
    ((densityExpansion_spec M hE κ D P').2 _ hjoin)

lemma densityExpansion_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
      κ * natRank M (Q ∪ Z) := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hQc : Q ⊆ M.closure (Q ∪ Z) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hmax := hQ.2.2 (M.closure (Q ∪ Z)) (Matroid.isFlat_closure (M := M) _) (hQ.2.1.trans hQc)
  have hc := Set.ncard_sdiff_add_ncard_of_subset (inter_subset_inter_right D hQc)
  have heq : D ∩ (M.closure (Q ∪ Z) \ Q) =
      (D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q) := by ext; simp; tauto
  change (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard + κ * natRank M Q ≤
    κ * natRank M (Q ∪ Z)
  rw [heq]
  dsimp [densityObjective] at hmax
  rw [natRank_closure] at hmax
  exact_mod_cast (show ((D ∩ M.closure (Q ∪ Z)) \ (D ∩ Q)).ncard +
    (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M (Q ∪ Z) by omega)

omit [Fintype α] in
lemma natRank_eq_ncard_of_basis (M : Matroid α) {I X : Set α}
    (hI : M.IsBasis I X) : natRank M X = I.ncard := by
  rw [natRank, ← hI.encard_eq_eRk, Set.ncard_def]

lemma closure_eq_of_subset_of_natRank_le (M : Matroid α) {X Y : Set α}
    (hXY : X ⊆ Y) (hr : natRank M Y ≤ natRank M X) : M.closure X = M.closure Y := by
  apply (M.isRkFinite_set X).closure_eq_closure_of_subset_of_eRk_ge_eRk hXY
  have hcast : (natRank M Y : ℕ∞) ≤ (natRank M X : ℕ∞) := by exact_mod_cast hr
  simpa only [natRank, ENat.natCast_toNat (rank_ne_top M _)] using hcast

lemma densityExpansion_generated (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P : Set α) :
    let Q := densityExpansion M hE κ D P
    M.closure (P ∪ (D ∩ Q)) = Q := by
  dsimp only
  let Q := densityExpansion M hE κ D P
  let A := M.closure (P ∪ (D ∩ Q))
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hAQ : A ⊆ Q := by
    exact (M.closure_subset_closure (union_subset hQ.2.1 inter_subset_right)).trans_eq hQ.1.closure
  have hPA : P ⊆ A := subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hDA : D ∩ A = D ∩ Q := by
    apply Subset.antisymm (inter_subset_inter_right D hAQ)
    exact fun e he => ⟨he.1, M.subset_closure _ (by simp [hE]) (Or.inr he)⟩
  have hm := hQ.2.2 A (Matroid.isFlat_closure (M := M) _) hPA
  have hr : natRank M Q ≤ natRank M A := by
    dsimp [densityObjective] at hm
    rw [hDA] at hm
    have hm' : (κ : ℤ) * natRank M Q ≤ (κ : ℤ) * natRank M A := by omega
    have hk' : (0 : ℤ) < κ := by exact_mod_cast hκ
    exact_mod_cast (le_of_mul_le_mul_left hm' hk')
  have heq := closure_eq_of_subset_of_natRank_le M hAQ hr
  simpa only [A, M.closure_closure, hQ.1.closure] using heq

lemma exists_extension_generators (M : Matroid α) (hE : M.E = univ)
    (R D Q : Set α) (_hR : M.IsFlat R) (hgen : M.closure (R ∪ D) = Q) :
    ∃ K : Set α, K ⊆ D \ R ∧ M.closure (R ∪ K) = Q ∧
      K.ncard + natRank M R = natRank M Q := by
  obtain ⟨I, hI, hIR⟩ := M.exists_isBasis_union_inter_isBasis D R
    (by simp [hE]) (by simp [hE])
  refine ⟨I \ R, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨?_, he.2⟩
    rcases hI.subset he.1 with hD | hr
    · exact hD
    · exact (he.2 hr).elim
  · apply Subset.antisymm
    · have hsub : R ∪ (I \ R) ⊆ R ∪ D := by
        intro e he
        rcases he with hr | hi
        · exact Or.inl hr
        · rcases hI.subset hi.1 with hd | hr
          · exact Or.inr hd
          · exact Or.inl hr
      exact (M.closure_subset_closure hsub).trans_eq hgen
    · have hIsub : I ⊆ R ∪ (I \ R) := by intro e he; by_cases hr : e ∈ R <;> simp_all
      calc
        Q = M.closure (D ∪ R) := by rw [union_comm D R, hgen]
        _ = M.closure I := hI.closure_eq_closure.symm
        _ ⊆ M.closure (R ∪ (I \ R)) := M.closure_subset_closure hIsub
  · have hiRank : natRank M Q = I.ncard := by
      rw [← hgen, natRank_closure, union_comm R D]
      exact natRank_eq_ncard_of_basis M hI
    rw [natRank_eq_ncard_of_basis M hIR, hiRank]
    simpa only [add_comm] using Set.ncard_inter_add_ncard_sdiff_eq_ncard I R

lemma densityExpansion_generator_step (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D P R : Set α) (hR : M.IsFlat R)
    (hPR : P ⊆ R) (hRQ : R ⊆ densityExpansion M hE κ D P) :
    ∃ K : Set α,
      K ⊆ (D ∩ densityExpansion M hE κ D P) \ R ∧
      M.closure (R ∪ K) = densityExpansion M hE κ D P ∧
      κ * K.ncard + (D ∩ R).ncard ≤
        (D ∩ densityExpansion M hE κ D P).ncard := by
  let Q := densityExpansion M hE κ D P
  have hQ : IsDensityMax M κ D P Q := (densityExpansion_spec M hE κ D P).1
  have hgen : M.closure (R ∪ (D ∩ Q)) = Q := by
    apply Subset.antisymm
    · exact (M.closure_subset_closure (union_subset hRQ inter_subset_right)).trans_eq hQ.1.closure
    · calc
        Q = M.closure (P ∪ (D ∩ Q)) := (densityExpansion_generated M hE κ hκ D P).symm
        _ ⊆ M.closure (R ∪ (D ∩ Q)) :=
          M.closure_subset_closure (union_subset_union hPR Subset.rfl)
  obtain ⟨K, hK, hKgen, hKcard⟩ := exists_extension_generators M hE R (D ∩ Q) Q hR hgen
  refine ⟨K, hK, hKgen, ?_⟩
  have hm := hQ.2.2 R hR hPR
  dsimp [densityObjective] at hm
  have hmul := congrArg (fun x : ℕ => κ * x) hKcard
  rw [Nat.mul_add] at hmul
  exact_mod_cast (show (κ : ℤ) * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q).ncard by
    have hmul' : (κ : ℤ) * K.ncard + (κ : ℤ) * natRank M R =
        (κ : ℤ) * natRank M Q := by exact_mod_cast hmul
    omega)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Path
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set

variable {α : Type*} [Fintype α]

private lemma densityPath_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ J : ℕ → Set α, Monotone J ∧ (∀ k, J k ⊆ D) ∧
      (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) ∧
      κ * (J N).ncard ≤ (D ∩ densityExpansion M hE κ D (P N)).ncard ∧
      (∀ k, N ≤ k → J k = J N) := by
  induction N with
  | zero =>
    have hPQ : M.closure (P 0) ⊆ densityExpansion M hE κ D (P 0) := by
      exact (M.closure_subset_closure (densityExpansion_extensive M hE κ D (P 0))).trans_eq
        (densityExpansion_flat M hE κ D (P 0)).closure
    obtain ⟨K, hK, hgen, hcard⟩ := densityExpansion_generator_step M hE κ hκ D (P 0)
      (M.closure (P 0)) (Matroid.isFlat_closure (M := M) _)
      (M.subset_closure _ (by simp [hE])) hPQ
    refine ⟨fun _ => K, fun _ _ _ => Subset.rfl, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ he => (hK he).1.1
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa only [M.closure_union_closure_left_eq] using hgen
    · dsimp only
      omega
    · exact fun _ _ => rfl
  | succ N ih =>
    obtain ⟨J, hJmono, hJD, hJgen, hJcard, hJsat⟩ := ih
    let Q := densityExpansion M hE κ D (P N)
    let Q' := densityExpansion M hE κ D (P (N + 1))
    let R := M.closure (P (N + 1) ∪ Q)
    have hQQ' : Q ⊆ Q' := densityExpansion_mono M hE κ D (hP (Nat.le_succ N))
    have hRflat : M.IsFlat R := Matroid.isFlat_closure (M := M) _
    have hPR : P (N + 1) ⊆ R :=
      subset_union_left.trans (M.subset_closure _ (by simp [hE]))
    have hQR : Q ⊆ R := subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hRQ' : R ⊆ Q' := by
      exact (M.closure_subset_closure
        (union_subset (densityExpansion_extensive M hE κ D _) hQQ')).trans_eq
        (densityExpansion_flat M hE κ D _).closure
    obtain ⟨K, hK, hKgen, hKcard⟩ :=
      densityExpansion_generator_step M hE κ hκ D (P (N + 1)) R hRflat hPR hRQ'
    have hJNQ : J N ⊆ Q := by
      change J N ⊆ densityExpansion M hE κ D (P N)
      rw [← hJgen N le_rfl]
      exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))
    have hJNR : J N ⊆ R := hJNQ.trans hQR
    have hdisj : Disjoint (J N) K := by
      rw [Set.disjoint_left]
      intro e heJ heK
      exact (hK heK).2 (hJNR heJ)
    have hRgen : M.closure (P (N + 1) ∪ J N) = R := by
      apply Subset.antisymm
      · exact M.closure_subset_closure (union_subset_union Subset.rfl hJNQ)
      · apply Matroid.closure_subset_closure_of_subset_closure
        apply union_subset
        · exact subset_union_left.trans (M.subset_closure _ (by simp [hE]))
        · change densityExpansion M hE κ D (P N) ⊆ _
          rw [← hJgen N le_rfl]
          exact M.closure_subset_closure (union_subset_union (hP (Nat.le_succ N)) Subset.rfl)
    have hnewgen : M.closure (P (N + 1) ∪ (J N ∪ K)) = Q' := by
      calc
        M.closure (P (N + 1) ∪ (J N ∪ K)) =
            M.closure ((P (N + 1) ∪ J N) ∪ K) := by rw [union_assoc]
        _ = M.closure (M.closure (P (N + 1) ∪ J N) ∪ K) :=
          (M.closure_union_closure_left_eq _ _).symm
        _ = M.closure (R ∪ K) := by rw [hRgen]
        _ = Q' := hKgen
    have hnewcard : κ * (J N ∪ K).ncard ≤ (D ∩ Q').ncard := by
      rw [Set.ncard_union_eq hdisj, Nat.mul_add]
      have hm := Set.ncard_mono (inter_subset_inter_right D hQR)
      change κ * K.ncard + (D ∩ R).ncard ≤ (D ∩ Q').ncard at hKcard
      change κ * (J N).ncard ≤ (D ∩ Q).ncard at hJcard
      omega
    let J' : ℕ → Set α := fun k => if k ≤ N then J k else J N ∪ K
    have hJ'last : J' (N + 1) = J N ∪ K := by simp [J']
    refine ⟨J', ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i ≤ N
      · by_cases hj : j ≤ N
        · simpa [J', hi, hj] using hJmono hij
        · change (if i ≤ N then J i else J N ∪ K) ⊆ _
          rw [ite_eq_left hi]
          simpa only [J', ite_eq_right hj] using (hJmono hi).trans subset_union_left
      · have hj : ¬j ≤ N := by omega
        simp only [J', ite_eq_right hi, ite_eq_right hj]
        exact Subset.rfl
    · intro k e he
      by_cases hk : k ≤ N
      · exact hJD k (by simpa [J', hk] using he)
      · have he' : e ∈ J N ∪ K := by simpa [J', hk] using he
        rcases he' with heJ | heK
        · exact hJD N heJ
        · exact (hK heK).1.1
    · intro k hk
      by_cases hk' : k ≤ N
      · simpa [J', hk'] using hJgen k hk'
      · have heq : k = N + 1 := by omega
        subst k
        rw [hJ'last]
        exact hnewgen
    · rw [hJ'last]
      exact hnewcard
    · intro k hk
      have hk' : ¬ k ≤ N := by omega
      rw [hJ'last]
      simp [J', hk']

lemma densityPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D : Set α) (P : ℕ → Set α) (hP : Monotone P) (N : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D ∧ κ * Jtotal.ncard ≤ D.ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ k ≤ N, J k ⊆ Jtotal) ∧
        (∀ k ≤ N, M.closure (P k ∪ J k) = densityExpansion M hE κ D (P k)) := by
  obtain ⟨J, hmono, hD, hgen, hcard, _⟩ := densityPath_prefix M hE κ hκ D P hP N
  refine ⟨J N, hD N, ?_, J, hmono, ?_, hgen⟩
  · exact hcard.trans (Set.ncard_mono inter_subset_left)
  · exact fun k hk => hmono hk

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Guarded
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma densityEnabled_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a : ℤ) {k k' : ℤ} {P P' : Set α}
    (hkk' : k ≤ k') (hPP' : P ⊆ P') :
    densityEnabled M hE κ D a k P ⊆ densityEnabled M hE κ D a k' P' := by
  by_cases hak : a ≤ k
  · have hak' := hak.trans hkk'
    simpa only [densityEnabled, ite_eq_left hak, ite_eq_left hak'] using
      densityExpansion_mono M hE κ D hPP'
  · by_cases hak' : a ≤ k'
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_left hak'] using
        hPP'.trans (densityExpansion_extensive M hE κ D P')
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_right hak'] using hPP'

lemma guardedPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (guardedPath M hE κ D C h) := by
  induction h with
  | zero =>
    intro i j hij
    by_cases hi : i < 0
    · by_cases hj : j < 0
      · simp only [guardedPath, ite_eq_left hi, ite_eq_left hj, Subset.rfl]
      · simp only [guardedPath, ite_eq_left hi, ite_eq_right hj, subset_univ]
    · have hj : ¬ j < 0 := by omega
      simp only [guardedPath, ite_eq_right hi, ite_eq_right hj, Subset.rfl]
  | succ h ih =>
    intro i j hij
    apply M.closure_subset_closure
    exact union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hij (ih hij))
      (inter_subset_inter_right (C h)
        (densityEnabled_mono M hE κ (D h) (activation h) (by omega) (ih (by omega))))

lemma nominalPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (nominalPath M hE κ D C h) := by
  intro i j hij
  exact densityEnabled_mono M hE κ (D h) (activation h) hij
    (guardedPath_mono M hE κ D C h hij)

lemma guarded_subset_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k :=
  densityEnabled_extensive M hE κ (D h) (activation h) k _

lemma nominal_subset_guarded (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h+1) k :=
  subset_union_left.trans (M.subset_closure _ (by simp [hE]))

lemma guardedPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < -3 * (h : ℤ) - 1) :
    guardedPath M hE κ D C h k = M.closure ∅ := by
  induction h generalizing k with
  | zero =>
    have hk' : k < 0 := by omega
    simp [guardedPath, hk']
  | succ h ih =>
    have hka : ¬ activation h ≤ k := by dsimp [activation]; push_cast at hk; omega
    have hk'a : ¬ activation h ≤ k+1 := by dsimp [activation]; push_cast at hk; omega
    have hkold : k < -3 * (h : ℤ) - 1 := by push_cast at hk; omega
    have hk'old : k+1 < -3 * (h : ℤ) - 1 := by omega
    rw [guardedPath, densityEnabled, densityEnabled, ite_eq_right hka, ite_eq_right hk'a,
      ih hkold, ih hk'old]
    rw [union_eq_self_of_subset_right inter_subset_right, M.closure_closure]

lemma nominalPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < activation h) :
    nominalPath M hE κ D C h k = M.closure ∅ := by
  rw [nominalPath, densityEnabled, ite_eq_right (not_le_of_gt hk)]
  apply guardedPath_early
  dsimp [activation] at hk
  omega

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Density_Birth
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma nominalPath_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ Jtotal : Set α, Jtotal ⊆ D h ∧ κ * Jtotal.ncard ≤ (D h).ncard ∧
      ∃ J : ℕ → Set α, Monotone J ∧ (∀ j ≤ pathHorizon h, J j ⊆ Jtotal) ∧
        (∀ j ≤ pathHorizon h,
          M.closure (guardedPath M hE κ D C h (activation h + j) ∪ J j) =
            nominalPath M hE κ D C h (activation h + j)) := by
  have hmono : Monotone (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) := by
    intro i j hij
    apply guardedPath_mono M hE κ D C h
    have hi : (i : ℤ) ≤ j := by exact_mod_cast hij
    omega
  obtain ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, hgen⟩ :=
    densityPath_generators M hE κ hκ (D h)
      (fun j : ℕ => guardedPath M hE κ D C h (activation h + j)) hmono (pathHorizon h)
  refine ⟨Jtotal, hJD, hcard, J, hJmono, hJJ, ?_⟩
  intro j hj
  rw [nominalPath, densityEnabled, ite_eq_left (by omega)]
  exact hgen j hj

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FiniteBits
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_mono (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S ≤ g S) :
    bitsExpectation q V f ≤ bitsExpectation q V g := by
  apply sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS)) (bitsWeight_nonneg q hq0 hq1 V S)

lemma bitsExpectation_congr (q : α → ℝ) (V : Finset α)
    {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S = g S) :
    bitsExpectation q V f = bitsExpectation q V g := by
  apply sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.1 hS)]

lemma bitsExpectation_add (q : α → ℝ) (V : Finset α) (f g : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S + g S) =
      bitsExpectation q V f + bitsExpectation q V g := by
  simp only [bitsExpectation, mul_add, sum_add_distrib]

lemma bitsExpectation_const (q : α → ℝ) (V : Finset α) (c : ℝ) :
    bitsExpectation q V (fun _ => c) = c := by
  have h := bitsExpectation_one q V
  simp only [bitsExpectation, mul_one] at h
  simp only [bitsExpectation, ← sum_mul, h, one_mul]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_RankAccounting
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α]

lemma conditionalRank_add_base (M : Matroid α) (S P : Set α) :
    conditionalRank M S P + natRank M P = natRank M (S ∪ P) := by
  exact Nat.sub_add_cancel (natRank_mono M subset_union_right)

lemma conditionalRank_antitone (M : Matroid α) (S : Set α)
    {P Q : Set α} (hPQ : P ⊆ Q) :
    conditionalRank M S Q ≤ conditionalRank M S P := by
  have hsub := natRank_submod M (S ∪ P) Q
  have hi := natRank_mono M (show P ⊆ (S ∪ P) ∩ Q from
    fun x hx => ⟨Or.inr hx, hPQ hx⟩)
  have hu : (S ∪ P) ∪ Q = S ∪ Q := by
    ext x
    simp only [mem_union]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hPQ h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  rw [hu] at hsub
  have hP := conditionalRank_add_base M S P
  have hQ := conditionalRank_add_base M S Q
  omega

lemma conditionalRank_exchange (M : Matroid α) (S J A : Set α) :
    conditionalRank M S A + conditionalRank M J (A ∪ S) =
      conditionalRank M J A + conditionalRank M S (A ∪ J) := by
  have hSA := conditionalRank_add_base M S A
  have hJA := conditionalRank_add_base M J A
  have hJAS := conditionalRank_add_base M J (A ∪ S)
  have hSAJ := conditionalRank_add_base M S (A ∪ J)
  have hUS : S ∪ A = A ∪ S := union_comm _ _
  have hUJ : J ∪ A = A ∪ J := union_comm _ _
  have hU : J ∪ (A ∪ S) = S ∪ (A ∪ J) := by
    ext x
    simp only [mem_union]
    tauto
  rw [hUS] at hSA
  rw [hUJ] at hJA
  rw [hU] at hJAS
  omega

lemma sum_potential_drop_le (p : ℕ → ℕ) (m : ℕ)
    (hp : ∀ k < m, p (k + 1) ≤ p k) :
    (∑ k ∈ range m, (p k - p (k + 1))) ≤ p 0 := by
  suffices h : (∑ k ∈ range m, (p k - p (k + 1))) + p m = p 0 by omega
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hprev := ih (fun k hk => hp k (Nat.lt_trans hk (Nat.lt_succ_self m)))
    have hlast := hp m (Nat.lt_succ_self m)
    omega

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Groups
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset

variable {n : ℕ}

lemma groups_sorted (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) : (groups M d seen).SortedLT :=
  Finset.sortedLT_sort _

lemma groups_get?_idxOf (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (i : ℤ) (hi : i ∈ groups M d seen) :
    (groups M d seen)[(groups M d seen).idxOf i]? = some i :=
  List.getElem?_idxOf hi

lemma groups_earlier_key (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) {j h : ℕ} {i : ℤ}
    (hh : (groups M d seen)[h]? = some i) (hjh : j < h) :
    ∃ k, (groups M d seen)[j]? = some k ∧ k < i := by
  obtain ⟨hh', hi⟩ := List.getElem?_eq_some_iff.mp hh
  have hj : j < (groups M d seen).length := hjh.trans hh'
  refine ⟨(groups M d seen)[j], List.getElem?_eq_getElem hj, ?_⟩
  rw [← hi]
  exact (groups_sorted M d seen).getElem_lt_getElem_of_lt hjh

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ProductRestriction
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_sum {ι : Type*} (q : α → ℝ) (V : Finset α) (I : Finset ι)
    (f : ι → Finset α → ℝ) :
    bitsExpectation q V (fun S => ∑ e ∈ I, f e S) = ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_ProductSplit
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma bitsExpectation_comm (p : α → ℝ) (q : β → ℝ) (U : Finset α) (V : Finset β)
    (f : Finset α → Finset β → ℝ) :
    bitsExpectation p U (fun S => bitsExpectation q V (f S)) =
      bitsExpectation q V (fun T => bitsExpectation p U (fun S => f S T)) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_disjoint_union (q : α → ℝ) (U V : Finset α) (hUV : Disjoint U V)
    (f : Finset α → ℝ) :
    bitsExpectation q (U ∪ V) f =
      bitsExpectation q U (fun S => bitsExpectation q V (fun T => f (S ∪ T))) := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp only [empty_union, bitsExpectation_empty]
  | @insert e U he ih =>
    have heV : e ∉ V := fun hx => (Finset.disjoint_left.mp hUV (mem_insert_self e U) hx)
    have hU : Disjoint U V := hUV.mono_left (subset_insert e U)
    rw [insert_union, bitsExpectation_insert q (U ∪ V) e (by simp [he, heV]),
      bitsExpectation_insert q U e he, ih hU f, ih hU (fun S => f (insert e S))]
    simp only [insert_union]

lemma bitsExpectation_split (q : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → ℝ) :
    bitsExpectation q V f =
      bitsExpectation q (V \ U) (fun S => bitsExpectation q U (fun T => f (S ∪ T))) := by
  have heq : (V \ U) ∪ U = V := sdiff_union_of_subset hU
  rw [← bitsExpectation_disjoint_union q (V \ U) U sdiff_disjoint f, heq]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Basic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

variable {α : Type*} {M : Matroid α} {I J : Set α} {e : α}

lemma support_subset (he : e ∈ M.closure I) : support M I e ⊆ I :=
  Set.sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma support_subset_of_mem_closure (hJI : J ⊆ I) (he : e ∈ M.closure J) :
    support M I e ⊆ J :=
  Set.sInter_subset_of_mem ⟨hJI, he⟩

lemma mem_closure_support (hI : M.Indep I) (he : e ∈ M.closure I) :
    e ∈ M.closure (support M I e) := by
  rw [support, hI.closure_sInter_eq_biInter_closure_of_forall_subset
    (Js := {J | J ⊆ I ∧ e ∈ M.closure J})
    ⟨I, Subset.rfl, he⟩ (fun _ hJ => hJ.1)]
  exact Set.mem_iInter₂.mpr (fun _ hJ => hJ.2)

lemma mem_closure_iff_support_subset (hI : M.Indep I)
    (he : e ∈ M.closure I) (hJI : J ⊆ I) :
    e ∈ M.closure J ↔ support M I e ⊆ J := by
  constructor
  · exact support_subset_of_mem_closure hJI
  · intro h
    exact M.closure_subset_closure h (mem_closure_support hI he)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_GreedyScan
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma mem_closure_kept_upto (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (o : β) :
    label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ time o}) := by
  classical
  have aux : ∀ k, ∀ o, time o = k →
      label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro o ho
      by_cases hkeep : o ∈ keptOccurrences M label time
      · exact M.mem_closure_of_mem ⟨o, ⟨hkeep, ho.le⟩, rfl⟩
          (by rintro _ ⟨p, _, rfl⟩; exact hground p)
      have hdep : label o ∈ M.closure (label '' {p | time p < time o}) := by
        simpa [keptOccurrences] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro _ ⟨p, hp, rfl⟩
      have hpk : time p < k := by simpa [ho] using hp
      have hih := ih (time p) hpk p rfl
      apply M.closure_subset_closure ?_ hih
      rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
      exact ⟨q, ⟨hq, hqt.trans hpk.le⟩, rfl⟩
  exact aux (time o) o rfl

lemma greedy_prefix_closure (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (k : ℕ) :
    M.closure (label '' {o | time o < k}) =
      M.closure (label '' {o | o ∈ keptOccurrences M label time ∧ time o < k}) := by
  classical
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro _ ⟨o, ho, rfl⟩
    apply M.closure_subset_closure ?_ (mem_closure_kept_upto M label time hground o)
    rintro _ ⟨p, ⟨hp, hpt⟩, rfl⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hpt ho⟩, rfl⟩
  · apply M.closure_subset_closure
    rintro _ ⟨o, ⟨_, ho⟩, rfl⟩
    exact ⟨o, ho, rfl⟩

private lemma indep_image_of_notMem_prior
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β] (M : Matroid α) (label : β → α)
    (time : β → ℕ) (htime : Function.Injective time) (s : Finset β)
    (hground : ∀ o ∈ s, label o ∈ M.E)
    (hprior : ∀ o ∈ s, label o ∉ M.closure (label '' {p | p ∈ s ∧ time p < time o})) :
    M.Indep (label '' (s : Set β)) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image s time (Finset.nonempty_iff_ne_empty.mpr hs)
    have hI := ih (s.erase p) (Finset.erase_ssubset hp)
      (fun o ho => hground o (Finset.mem_of_mem_erase ho)) (by
        intro o ho hmem
        apply hprior o (Finset.mem_of_mem_erase ho)
        apply M.closure_subset_closure ?_ hmem
        rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
        exact ⟨q, ⟨Finset.mem_of_mem_erase hq, hqt⟩, rfl⟩)
    have hnot : label p ∉ M.closure (label '' (s.erase p : Set β)) := by
      intro hmem
      apply hprior p hp
      apply M.closure_subset_closure ?_ hmem
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨q, ⟨Finset.mem_of_mem_erase hq, ?_⟩, rfl⟩
      apply lt_of_le_of_ne (hmax q (Finset.mem_of_mem_erase hq))
      intro htimeeq
      exact (Finset.ne_of_mem_erase hq) (htime htimeeq)
    have hins := hI.insert_indep_iff.mpr (Or.inl ⟨hground p hp, hnot⟩)
    have hset : insert (label p) (label '' (s.erase p : Set β)) = label '' (s : Set β) := by
      rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]
    rwa [hset] at hins

lemma keptOccurrences_indep (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    M.Indep (label '' (keptOccurrences M label time : Set β)) := by
  classical
  apply indep_image_of_notMem_prior M label time htime
  · intro o _
    exact hground o
  · intro o ho hmem
    have hn := (Finset.mem_filter.mp ho).2
    apply hn
    apply M.closure_subset_closure ?_ hmem
    rintro _ ⟨p, ⟨_, hpt⟩, rfl⟩
    exact ⟨p, hpt, rfl⟩

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_OccurrenceSupport
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma kept_label_injOn
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    Set.InjOn label (keptOccurrences M label time : Set β) := by
  classical
  have hd : ∀ x y, x ∈ keptOccurrences M label time → y ∈ keptOccurrences M label time →
      time x < time y → label x ≠ label y := by
    intro x y _ hy hxy hlabels
    apply (Finset.mem_filter.mp hy).2
    rw [← hlabels]
    exact M.mem_closure_of_mem ⟨x, hxy, rfl⟩ (by rintro _ ⟨z, _, rfl⟩; exact hground z)
  intro x hx y hy hlabels
  apply htime
  rcases lt_trichotomy (time x) (time y) with hlt | heq | hgt
  · exact False.elim (hd x y hx hy hlt hlabels)
  · exact heq
  · exact False.elim (hd y x hy hx hgt hlabels.symm)

lemma mem_occurrenceSupport
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    {M : Matroid α} {label : β → α} {J : Finset β} {e : α} {o : β} :
    o ∈ occurrenceSupport M label J e ↔
      o ∈ J ∧ label o ∈ support M (label '' (J : Set β)) e := by
  classical
  simp [occurrenceSupport]

lemma mem_closure_iff_occurrenceSupport (M : Matroid α) (label : β → α)
    (J : Finset β) (e : α) (hI : M.Indep (label '' (J : Set β)))
    (he : e ∈ M.closure (label '' (J : Set β)))
    (hinj : Set.InjOn label (J : Set β)) (P : β → Prop) :
    e ∈ M.closure (label '' {o | o ∈ J ∧ P o}) ↔
      ∀ o ∈ occurrenceSupport M label J e, P o := by
  classical
  rw [mem_closure_iff_support_subset hI he (by
    rintro _ ⟨o, ⟨ho, _⟩, rfl⟩; exact ⟨o, ho, rfl⟩)]
  constructor
  · intro h o ho
    obtain ⟨hoJ, hol⟩ := mem_occurrenceSupport.mp ho
    obtain ⟨p, ⟨hpJ, hpP⟩, hp⟩ := h hol
    exact (hinj hpJ hoJ hp) ▸ hpP
  · intro h x hx
    obtain ⟨o, ho, rfl⟩ := support_subset he hx
    exact ⟨o, ⟨ho, h o (mem_occurrenceSupport.mpr ⟨ho, hx⟩)⟩, rfl⟩

lemma pivot_mem_support_and_max (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time)
    {e : α} {o : β} (hpivot : IsPivot M label time e o) :
    o ∈ occurrenceSupport M label (keptOccurrences M label time) e ∧
      ∀ p ∈ occurrenceSupport M label (keptOccurrences M label time) e, time p ≤ time o := by
  classical
  let J := keptOccurrences M label time
  have hI := keptOccurrences_indep M label time hground htime
  have hinj := kept_label_injOn M label time hground htime
  have hup : e ∈ M.closure (label '' {p | p ∈ J ∧ time p ≤ time o}) := by
    have h := hpivot.1
    have hcl := greedy_prefix_closure M label time hground (time o + 1)
    simp only [Nat.lt_succ_iff] at hcl
    rw [hcl] at h
    exact h
  have he : e ∈ M.closure (label '' (J : Set β)) := by
    apply M.closure_subset_closure ?_ hup
    rintro _ ⟨p, ⟨hp, _⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hmax := (mem_closure_iff_occurrenceSupport M label J e hI he hinj
    (fun p => time p ≤ time o)).mp hup
  have hnot : ¬ ∀ p ∈ occurrenceSupport M label J e, time p < time o := by
    intro h
    apply hpivot.2
    rw [greedy_prefix_closure M label time hground (time o)]
    exact (mem_closure_iff_occurrenceSupport M label J e hI he hinj
      (fun p => time p < time o)).mpr h
  push Not at hnot
  obtain ⟨p, hp, hge⟩ := hnot
  have heq : p = o := htime (Nat.le_antisymm (hmax p hp) hge)
  exact ⟨heq ▸ hp, hmax⟩

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Existence
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma exists_pivot
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ) {e : α}
    (hnonloop : e ∉ M.closure ∅) (hspan : e ∈ M.closure (Set.range label)) :
    ∃ o, IsPivot M label time e o := by
  classical
  let P := fun k => e ∈ M.closure (label '' {o | time o ≤ k})
  have hex : ∃ k, P k := by
    refine ⟨Finset.univ.sup time, M.closure_subset_closure ?_ hspan⟩
    rintro _ ⟨o, rfl⟩
    exact ⟨o, by
      change time o ≤ Finset.univ.sup time
      exact Finset.le_sup (Finset.mem_univ o), rfl⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hnot : e ∉ M.closure (label '' {o | time o < k}) := by
    intro hn
    by_cases hk0 : k = 0
    · exact hnonloop (by simpa [hk0] using hn)
    have hprev : P (k - 1) := by
      apply M.closure_subset_closure ?_ hn
      rintro _ ⟨o, ho, rfl⟩
      exact ⟨o, by
        change time o ≤ k - 1
        change time o < k at ho
        omega, rfl⟩
    have hmin : k ≤ k - 1 := Nat.find_min' hex hprev
    omega
  have hat : ∃ o, time o = k := by
    by_contra h
    apply hnot
    apply M.closure_subset_closure ?_ hk
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    have hne : time o ≠ k := fun heq => h ⟨o, heq⟩
    change time o < k
    change time o ≤ k at ho
    omega
  obtain ⟨o, ho⟩ := hat
  exact ⟨o, by simpa [IsPivot, ho] using And.intro hk hnot⟩

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Count
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

variable {α : Type*} [DecidableEq α]

lemma card_family_with_fixed_core (family : Finset (Finset α))
    (core extra : Finset α)
    (hcore : ∀ J ∈ family, core ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ core ∪ extra) :
    family.card ≤ 2 ^ extra.card := by
  rw [← Finset.card_powerset extra]
  apply Finset.card_le_card_of_injOn (fun J => J \ core)
  · intro J hJ
    apply Finset.mem_powerset.mpr
    intro x hx
    have hcov := hcover J hJ (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_union.mp hcov).resolve_left (Finset.mem_sdiff.mp hx).2
  · intro J hJ K hK heq
    apply Finset.ext
    intro x
    by_cases hx : x ∈ core
    · exact iff_of_true (hcore J hJ hx) (hcore K hK hx)
    · have hmem := congrArg (fun L : Finset α => x ∈ L) heq
      simpa [Finset.mem_sdiff, hx] using hmem

lemma card_retained_family (family : Finset (Finset α))
    (old movable omittable : Finset α) (s : ℕ)
    (hm : movable.card ≤ s) (ho : omittable.card ≤ s)
    (hcore : ∀ J ∈ family, old \ omittable ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ old ∪ movable) :
    family.card ≤ 4 ^ s := by
  have h := card_family_with_fixed_core family (old \ omittable)
    (omittable ∪ movable) hcore (by
      intro J hJ x hx
      rcases Finset.mem_union.mp (hcover J hJ hx) with hxold | hxmov
      · by_cases hxo : x ∈ omittable
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxo)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxold, hxo⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxmov))
  have hcard : (omittable ∪ movable).card ≤ 2 * s :=
    (Finset.card_union_le _ _).trans (by omega)
  calc
    family.card ≤ 2 ^ (omittable ∪ movable).card := h
    _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by decide) hcard
    _ = 4 ^ s := by rw [pow_mul]; rfl

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Greedy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

lemma oldPrefix_succ
    {α : Type u_1} [Fintype α] (b : ℕ → α) (k : ℕ) :
    oldPrefix b (k + 1) = insert (b k) (oldPrefix b k) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), rfl⟩

lemma oldPrefix_mono
    {α : Type u_1} [Fintype α] (b : ℕ → α) : Monotone (oldPrefix b) := by
  intro j k hjk x hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, lt_of_lt_of_le hi hjk, rfl⟩

lemma conditionalRank_singleton_of_notMem_closure (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.E) (hne : e ∉ M.closure P) :
    conditionalRank M {e} P = 1 := by
  unfold conditionalRank natRank
  rw [Set.singleton_union, M.eRk_insert_eq_add_one ⟨he, hne⟩,
    ENat.toNat_add (rank_ne_top M P) (by simp)]
  simp

lemma conditionalRank_singleton_of_mem_closure
    {α : Type u_1} [Fintype α] (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.closure P) :
    conditionalRank M {e} P = 0 := by
  have h := congrArg (natRank M) (M.closure_insert_eq_of_mem_closure he)
  simp only [natRank_closure] at h
  simp only [conditionalRank, Set.singleton_union, h, Nat.sub_self]

lemma omittable_drop (M : Matroid α) (b : ℕ → α) (A : Set α) (k : ℕ)
    (he : b k ∈ M.E) (hind : b k ∉ M.closure (oldPrefix b k))
    (homit : b k ∈ M.closure (oldPrefix b k ∪ A)) :
    conditionalRank M A (oldPrefix b (k + 1)) + 1 =
      conditionalRank M A (oldPrefix b k) := by
  have hex := conditionalRank_exchange M {b k} A (oldPrefix b k)
  rw [conditionalRank_singleton_of_notMem_closure M _ he hind,
    conditionalRank_singleton_of_mem_closure M _ homit] at hex
  rw [oldPrefix_succ, Set.union_singleton] at *
  omega

lemma notMem_closure_before_nonomittable
    {α : Type u_1} [Fintype α] (M : Matroid α) (b : ℕ → α)
    (A P : Set α) (r k : ℕ) (hk : k < r)
    (hkeep : k ∉ omittable M b A r) (hP : P ⊆ oldPrefix b k ∪ A) :
    b k ∉ M.closure P := by
  classical
  intro he
  apply hkeep
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
    M.closure_subset_closure hP he⟩

lemma card_vulnerable_le_rank (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ)
    (he : ∀ k < r, b k ∈ M.E) :
    (vulnerable M b A r).card ≤ natRank M A := by
  classical
  let p := fun k => conditionalRank M A (oldPrefix b k)
  have hp : ∀ k < r, p (k + 1) ≤ p k := by
    intro k _
    exact conditionalRank_antitone M A (oldPrefix_mono b (Nat.le_succ k))
  have hdrop := sum_potential_drop_le p r hp
  have hsum : (vulnerable M b A r).card ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ k ∈ vulnerable M b A r, 1) ≤
          ∑ k ∈ vulnerable M b A r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkr := Finset.mem_range.mp hk'.1
        have hd := omittable_drop M b A k (he k hkr) hk'.2.1 hk'.2.2
        change p (k + 1) + 1 = p k at hd
        omega
      _ ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _
          exact Nat.zero_le _
  have hzero : p 0 = natRank M A := by simp [p, conditionalRank]
  omega

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Interleavings
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

lemma before_old_subset
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    occurrenceLabel b a '' {p | time p < time (Sum.inl i)} ⊆
      oldPrefix b i.val ∪ Set.range a := by
  rintro x ⟨o, ho, rfl⟩
  cases o with
  | inl j =>
    left
    have hji : j < i := by
      by_contra hji
      rcases lt_or_eq_of_le (le_of_not_gt hji) with hij | rfl
      · exact Nat.lt_asymm (horder i j hij) ho
      · exact Nat.lt_irrefl _ ho
    exact ⟨j.val, hji, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

lemma retains_nonomittable_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : i.val ∉ omittable M b (Set.range a) r) :
    Sum.inl i ∈ retained M b a time := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact notMem_closure_before_nonomittable M b (Set.range a) _ r i.val i.isLt hi
    (before_old_subset b a time horder i)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Arbitrary
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

lemma oldPrefix_subset_before
    {α : Type u_1} [Fintype α] {r s : ℕ} (b : ℕ → α) (a : Fin s → α)
    (time : Occurrence r s → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldPrefix b i.val ⊆ occurrenceLabel b a '' {p | time p < time (Sum.inl i)} := by
  rintro x ⟨k, hk, rfl⟩
  let j : Fin r := ⟨k, lt_trans hk i.isLt⟩
  exact ⟨Sum.inl j, horder j i hk, rfl⟩

lemma retained_old_initially_nonredundant {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (time : Occurrence r s → ℕ) (horder : OldOrdered time)
    (i : Fin r) (hi : Sum.inl i ∈ retained M b a time) :
    b i.val ∉ M.closure (oldPrefix b i.val) := by
  classical
  intro hdep
  exact (Finset.mem_filter.mp hi).2
    (M.closure_subset_closure (oldPrefix_subset_before b a time horder i) hdep)

lemma card_retainedFamily_arbitrary_old {r s : ℕ} (M : Matroid α) (b : ℕ → α)
    (a : Fin s → α) (he : ∀ k < r, b k ∈ M.E) :
    (retainedFamily (r := r) M b a).card ≤ 4 ^ s := by
  classical
  let old : Finset (Occurrence r s) :=
    (Finset.univ.filter (fun i : Fin r => b i.val ∉ M.closure (oldPrefix b i.val))).image Sum.inl
  let movable : Finset (Occurrence r s) := Finset.univ.image Sum.inr
  let omissions : Finset (Occurrence r s) := old.filter (fun o =>
    match o with
    | Sum.inl i => i.val ∈ vulnerable M b (Set.range a) r
    | Sum.inr _ => False)
  have hmov : movable.card ≤ s := by
    simp [movable, Finset.card_image_of_injective, Sum.inr_injective]
  have homit : omissions.card ≤ (vulnerable M b (Set.range a) r).card := by
    apply Finset.card_le_card_of_injOn
      (fun o : Occurrence r s => Sum.elim Fin.val (fun _ => 0) o)
    · intro o ho
      have ho' := (Finset.mem_filter.mp ho).2
      cases o with
      | inl i => exact ho'
      | inr j => exact False.elim ho'
    · intro o ho p hp hop
      have ho' := (Finset.mem_filter.mp ho).2
      have hp' := (Finset.mem_filter.mp hp).2
      cases o with
      | inr i => exact False.elim ho'
      | inl i =>
        cases p with
        | inr j => exact False.elim hp'
        | inl j => exact congrArg Sum.inl (Fin.ext hop)
  have hrank : natRank M (Set.range a) ≤ (Set.range a).ncard := by
    exact ENat.toNat_le_toNat (M.eRk_le_encard _)
      (Set.toFinite (Set.range a)).encard_lt_top.ne
  have hrange : (Set.range a).ncard ≤ s := by
    simpa using (Set.ncard_image_le (f := a) (s := Set.univ))
  apply card_retained_family (retainedFamily M b a) old movable omissions s hmov
    (homit.trans ((card_vulnerable_le_rank M b (Set.range a) r he).trans
      (hrank.trans hrange)))
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    have hoo := (Finset.mem_sdiff.mp ho).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hoo
    have hind := (Finset.mem_filter.mp hi).2
    apply retains_nonomittable_old M b a time horder i
    intro hom
    have hom' := (Finset.mem_filter.mp hom).2
    have hv : i.val ∈ vulnerable M b (Set.range a) r :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hind, hom'⟩
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_filter.mpr ⟨hoo, hv⟩)
  · intro J hJ o ho
    obtain ⟨time, horder, rfl⟩ := (Finset.mem_filter.mp hJ).2
    cases o with
    | inl i =>
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        retained_old_initially_nonredundant M b a time horder i ho⟩, rfl⟩
    | inr j => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Encoding
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Finset

variable {r q : ℕ}

lemma oldBefore_mono (time : Occurrence r q → ℕ) : Monotone (oldBefore time) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 huv⟩

lemma oldBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin r) {t : ℕ}
    (hit : time (Sum.inl i) < t) :
    oldBefore time (time (Sum.inl i)) < oldBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin q) {t : ℕ}
    (hit : time (Sum.inr i) < t) :
    movableBefore time (time (Sum.inr i)) < movableBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_self_lt (time : Occurrence r q → ℕ) (i : Fin q) :
    movableBefore time (time (Sum.inr i)) < q := by
  have hcard : (Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < time (Sum.inr i))).card <
      (Finset.univ : Finset (Fin q)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hi : i ∈ (Finset.univ : Finset (Fin q)) := Finset.mem_univ _
    rw [← heq] at hi
    simp at hi
  simpa [movableBefore] using hcard

lemma old_time_lt_iff (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    (i j : Fin r) : time (Sum.inl i) < time (Sum.inl j) ↔ i < j := by
  refine ⟨fun hij => ?_, fun hij => horder i j hij⟩
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hji | rfl
  · exact Nat.lt_asymm (horder j i hji) hij
  · exact Nat.lt_irrefl _ hij

lemma oldBefore_self (time : Occurrence r q → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldBefore time (time (Sum.inl i)) = i.val := by
  unfold oldBefore
  have heq : Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < time (Sum.inl i)) =
      Finset.Iio i := by
    ext j
    simp [old_time_lt_iff time horder]
  rw [heq, Fin.card_Iio]

lemma scoreExponent_preserves_order (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    {o p : Occurrence r q} (hop : time o < time p) :
    scoreExponent s time o < scoreExponent s time p := by
  cases o with
  | inl i =>
    cases p with
    | inl j =>
      have hij := (old_time_lt_iff time horder i j).mp hop
      exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 1) (by omega)
    | inr j =>
      have hcnt := oldBefore_lt_after time i hop
      rw [oldBefore_self time horder i] at hcnt
      have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hcnt)
      simp only [Nat.succ_eq_add_one] at hmul
      simp only [scoreExponent]
      omega
  | inr i =>
    have hbound := lt_of_lt_of_le (movableBefore_self_lt time i) hqs
    have hmono := oldBefore_mono time (Nat.le_of_lt hop)
    cases p with
    | inl j =>
      rw [oldBefore_self time horder j] at hmono
      have hmul := Nat.mul_le_mul_left (s + 1) hmono
      simp only [scoreExponent, Nat.mul_add, Nat.mul_one]
      omega
    | inr j =>
      have hstrict := movableBefore_lt_after time i hop
      rcases Nat.eq_or_lt_of_le hmono with heq | hlt
      · simp only [scoreExponent]
        rw [heq]
        omega
      · have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hlt)
        simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
        simp only [scoreExponent]
        omega

lemma scoreExponent_injective (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time) :
    Function.Injective (scoreExponent s time) := by
  intro o p heq
  apply htime
  apply le_antisymm
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Scores
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

lemma sum_positive_iff_pivot_positive (s : Finset α) (w : α → ℝ) {p : α}
    (hp : p ∈ s) (hdom : ∑ i ∈ s.erase p, |w i| < |w p|) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  have habs : |∑ i ∈ s.erase p, w i| ≤ ∑ i ∈ s.erase p, |w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbounds := abs_le.mp habs
  have hsum : (∑ i ∈ s, w i) = (∑ i ∈ s.erase p, w i) + w p :=
    (Finset.sum_erase_add _ _ hp).symm
  rw [hsum]
  by_cases hwp : 0 ≤ w p
  · rw [abs_of_nonneg hwp] at hdom
    constructor <;> intro h <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hwp)] at hdom
    constructor <;> intro h <;> linarith

lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sum_two_pow_lt (s : Finset ℕ) (k : ℕ) (hsk : ∀ i ∈ s, i < k) :
    (∑ i ∈ s, (2 : ℝ)^i) < 2^k := by
  have hsub : s ⊆ Finset.range k := fun i hi => Finset.mem_range.mpr (hsk i hi)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => show 0 ≤ (2 : ℝ)^i from pow_nonneg (by norm_num) _)
  rw [sum_range_two_pow] at hle
  linarith

lemma sum_positive_iff_max_exponent (s : Finset α) (w : α → ℝ) (exponent : α → ℕ)
    (hinj : Function.Injective exponent) {p : α} (hp : p ∈ s)
    (hmax : ∀ i ∈ s, i ≠ p → exponent i < exponent p)
    (hw : ∀ i ∈ s, |w i| = 2 ^ exponent i) :
    0 < ∑ i ∈ s, w i ↔ 0 < w p := by
  apply sum_positive_iff_pivot_positive s w hp
  rw [hw p hp]
  calc
    (∑ i ∈ s.erase p, |w i|) = ∑ i ∈ s.erase p, (2 : ℝ) ^ exponent i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hw i (Finset.mem_of_mem_erase hi)
    _ = ∑ j ∈ (s.erase p).image exponent, (2 : ℝ) ^ j := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact hinj hij
    _ < 2 ^ exponent p := by
      apply sum_two_pow_lt
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Sign
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup X] [Module ℝ X]

lemma mem_affinePatterns {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {t : Finset ι} :
    t ∈ affinePatterns v c ↔ ∃ x, RealizesSigns v c t x := by
  classical
  simp [affinePatterns]

private lemma exists_positive_combination
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    ∃ x, 0 < ∑ i, a i * (v i x + c i) := by
  classical
  obtain ⟨x, hx⟩ := hreal (Finset.univ.filter (fun i => 0 < a i))
  have hpos (i : ι) (hai : 0 < a i) : 0 < v i x + c i := by
    simpa [RealizesSigns, hai] using hx i
  have hneg (i : ι) (hai : ¬ 0 < a i) : v i x + c i < 0 := by
    simpa [RealizesSigns, hai] using hx i
  refine ⟨x, Finset.sum_pos' (fun i _ => ?_) ?_⟩
  · by_cases hai : 0 < a i
    · exact mul_nonneg (le_of_lt hai) (le_of_lt (hpos i hai))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hai) (le_of_lt (hneg i hai))
  · obtain ⟨i, hi⟩ := ha
    refine ⟨i, Finset.mem_univ i, ?_⟩
    by_cases hai : 0 < a i
    · exact mul_pos hai (hpos i hai)
    · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt hai) hi) (hneg i hai)

omit [DecidableEq ι] in
private lemma sum_affine_eq_of_linear_combination_zero
    {v : ι → X →ₗ[ℝ] ℝ} (c : ι → ℝ) {a : ι → ℝ}
    (ha : ∑ i, a i • v i = 0) (x : X) :
    (∑ i, a i * (v i x + c i)) = ∑ i, a i * c i := by
  have hz := congrArg (fun f : X →ₗ[ℝ] ℝ => f x) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply] at hz
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hz, zero_add]

lemma linearIndependent_of_all_signs
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hreal : ∀ t : Finset ι, ∃ x, RealizesSigns v c t x) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  obtain ⟨x, hx⟩ := exists_positive_combination v c hreal a ⟨i, hi⟩
  obtain ⟨y, hy⟩ := exists_positive_combination v c hreal (fun j => -a j)
    ⟨i, neg_ne_zero.mpr hi⟩
  simp only [neg_mul, Finset.sum_neg_distrib] at hy
  rw [sum_affine_eq_of_linear_combination_zero c ha x] at hx
  rw [sum_affine_eq_of_linear_combination_zero c ha y] at hy
  linarith

lemma all_signs_of_shatters {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ}
    {s : Finset ι} (hs : (affinePatterns v c).Shatters s) :
    ∀ t : Finset s, ∃ x,
      RealizesSigns (fun i : s => v i) (fun i : s => c i) t x := by
  classical
  intro t
  obtain ⟨u, hu, hsu⟩ := hs (t := t.image Subtype.val) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property)
  obtain ⟨x, hx⟩ := mem_affinePatterns.mp hu
  refine ⟨x, fun i => ?_⟩
  have hi : (i : ι) ∈ u ↔ i ∈ t := by
    have heq := congrArg (fun z : Finset ι => (i : ι) ∈ z) hsu
    simpa [Finset.mem_image, i.property] using heq
  simpa only [hi] using hx i

lemma shatters_card_le_finrank [FiniteDimensional ℝ X]
    {v : ι → X →ₗ[ℝ] ℝ} {c : ι → ℝ} {s : Finset ι}
    (hs : (affinePatterns v c).Shatters s) : s.card ≤ Module.finrank ℝ X := by
  have hli := linearIndependent_of_all_signs
    (fun i : s => v i) (fun i : s => c i) (all_signs_of_shatters hs)
  have hc := hli.fintype_card_le_finrank
  simpa using hc

lemma card_affinePatterns_le [FiniteDimensional ℝ X]
    (v : ι → X →ₗ[ℝ] ℝ) (c : ι → ℝ) :
    (affinePatterns v c).card ≤
      ∑ k ∈ Finset.Iic (Module.finrank ℝ X), (Fintype.card ι).choose k := by
  classical
  have hdim : (affinePatterns v c).vcDim ≤ Module.finrank ℝ X := by
    unfold Finset.vcDim
    exact Finset.sup_le (fun s hs => shatters_card_le_finrank (Finset.mem_shatterer.mp hs))
  exact (Finset.card_le_card_shatterer _).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hdim)
        (fun _ _ _ => Nat.zero_le _)))

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Patterns
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

lemma abs_markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) :
    |markedScore s time oldMark movableMark o| = (2 : ℝ) ^ scoreExponent s time o := by
  unfold markedScore
  split <;> simp [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

lemma affineScore_eq_sum
    {α : Type u_1} [Fintype α] {r : ℕ} {q : ℕ} (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    patternLinear M label J e (fun i => markedScore s time oldMark movableMark (Sum.inr i)) +
      patternConstant M label J e s oldMark =
      ∑ o ∈ occurrenceSupport M label J e, markedScore s time oldMark movableMark o := by
  simp only [patternLinear, patternConstant, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  cases o <;> simp [coordinateScore, constantScore, fixedOldScore, markedScore,
    occurrenceMark, scoreExponent]
  all_goals rfl

lemma recordsPivots_affine (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (s : ℕ) (hqs : q ≤ s)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) (t : Finset (Fin n))
    (hrecords : RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t) :
    ∃ x, RealizesSigns
      (fun f => patternLinear M (occurrenceLabel b a) (retained M b a time) (test f))
      (fun f => patternConstant M (occurrenceLabel b a) (retained M b a time) (test f) s oldMark)
      t x := by
  classical
  let label : Occurrence r q → α := occurrenceLabel b a
  let J := retained M b a time
  let w := markedScore s time oldMark movableMark
  let exponent := scoreExponent s time
  refine ⟨fun i => w (Sum.inr i), ?_⟩
  intro f
  rw [affineScore_eq_sum]
  obtain ⟨o, hpivot, hmark⟩ := hrecords f
  have hp := pivot_mem_support_and_max M label time hground htime hpivot
  change o ∈ occurrenceSupport M label J (test f) ∧
    (∀ p ∈ occurrenceSupport M label J (test f), time p ≤ time o) at hp
  have hmax : ∀ p ∈ occurrenceSupport M label J (test f), p ≠ o → exponent p < exponent o := by
    intro p hp' hne
    apply scoreExponent_preserves_order s hqs time horder
    exact lt_of_le_of_ne (hp.2 p hp') (fun heq => hne (htime heq))
  have hexp := scoreExponent_injective s hqs time horder htime
  have habs : ∀ p ∈ occurrenceSupport M label J (test f), |w p| = 2 ^ exponent p :=
    fun p _ => abs_markedScore s time oldMark movableMark p
  have hpos := sum_positive_iff_max_exponent _ w exponent hexp hp.1 hmax habs
  have hneg := sum_positive_iff_max_exponent _ (fun p => -w p) exponent hexp hp.1 hmax
    (by intro p hp'; simpa using habs p hp')
  simp only [Finset.sum_neg_distrib, neg_pos] at hneg
  have hpow : (0 : ℝ) < 2 ^ exponent o := pow_pos (by norm_num) _
  by_cases hf : f ∈ t
  · simp only [hf, ↓reduceIte]
    apply hpos.mpr
    have hm := hmark.mpr hf
    simp [w, markedScore, hm]
  · simp only [hf, ↓reduceIte]
    apply hneg.mpr
    have hm : occurrenceMark oldMark movableMark o = false := by
      cases h : occurrenceMark oldMark movableMark o
      · rfl
      · exact False.elim (hf (hmark.mp h))
    simp [w, markedScore, hm]

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Guarantee
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

lemma card_markedPivotPatterns_le (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool) (s : ℕ) (hqs : q ≤ s)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) :
    (markedPivotPatterns M b a test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let family := retainedFamily (r := r) M b a
  let affine := fun J : Finset (Occurrence r q) => affinePatterns
    (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
    (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hsub : markedPivotPatterns M b a test oldMark ⊆ family.biUnion affine := by
    intro t ht
    obtain ⟨time, horder, htime, movableMark, hrecords⟩ := (Finset.mem_filter.mp ht).2
    apply Finset.mem_biUnion.mpr
    refine ⟨retained M b a time, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, rfl⟩
    · apply mem_affinePatterns.mpr
      exact recordsPivots_affine M b a test s hqs oldMark movableMark time horder htime hground t hrecords
  have hcard (J : Finset (Occurrence r q)) :
      (affine J).card ≤ ∑ k ∈ Finset.Iic q, n.choose k := by
    simpa [affine] using card_affinePatterns_le
      (fun f : Fin n => patternLinear M (occurrenceLabel b a) J (test f))
      (fun f : Fin n => patternConstant M (occurrenceLabel b a) J (test f) s oldMark)
  have hfamily : family.card ≤ 4 ^ s :=
    (card_retainedFamily_arbitrary_old M b a
      (fun k hk => hground (Sum.inl ⟨k, hk⟩))).trans
      (Nat.pow_le_pow_right (by decide) hqs)
  have hsum : (∑ k ∈ Finset.Iic q, n.choose k) ≤ ∑ k ∈ Finset.Iic s, n.choose k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hqs) (fun _ _ _ => Nat.zero_le _)
  calc
    (markedPivotPatterns M b a test oldMark).card ≤ (family.biUnion affine).card := Finset.card_le_card hsub
    _ ≤ ∑ J ∈ family, (affine J).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ family, ∑ k ∈ Finset.Iic q, n.choose k := Finset.sum_le_sum (fun J _ => hcard J)
    _ = family.card * (∑ k ∈ Finset.Iic q, n.choose k) := by simp
    _ ≤ 4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := Nat.mul_le_mul hfamily hsum

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Reindex
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α β γ O A : Type*} [Fintype α]

lemma isPivot_reindex
    {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype α]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (e : γ ≃ β) (f : α) (o : γ) :
    IsPivot M (label ∘ e) (time ∘ e) f o ↔ IsPivot M label time f (e o) := by
  have himage (p : β → Prop) : (label ∘ e) '' {x | p (e x)} = label '' {x | p x} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  unfold IsPivot
  simp only [Function.comp_apply] at himage ⊢
  rw [himage (fun x => time x ≤ time (e o)), himage (fun x => time x < time (e o))]

lemma card_freeMarkedPatterns_le [Fintype O] [LinearOrder O] [Fintype A]
    (M : Matroid α) (d : α) (oldLabel : O → α) (movableLabel : A → α)
    {n : ℕ} (test : Fin n → α) (oldMark : O → Bool)
    (s : ℕ) (hs : Fintype.card A ≤ s)
    (hground : ∀ o, Sum.elim oldLabel movableLabel o ∈ M.E) :
    (freeMarkedPatterns M oldLabel movableLabel test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k := by
  classical
  let eO := Fintype.orderIsoFinOfCardEq O rfl
  let eA := (Fintype.equivFin A).symm
  let e := Equiv.sumCongr eO.toEquiv eA
  let b : ℕ → α := fun k => if hk : k < Fintype.card O then oldLabel (eO ⟨k, hk⟩) else d
  let a : Fin (Fintype.card A) → α := movableLabel ∘ eA
  let m : Fin (Fintype.card O) → Bool := oldMark ∘ eO
  have hlabel : occurrenceLabel b a = Sum.elim oldLabel movableLabel ∘ e := by
    funext o
    cases o <;> simp [occurrenceLabel, b, a, e]
  have hsub : freeMarkedPatterns M oldLabel movableLabel test oldMark ⊆
      markedPivotPatterns M b a test m := by
    intro t ht
    obtain ⟨time, horder, htime, mark, hrecord⟩ := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, time ∘ e, ?_, htime.comp e.injective,
      mark ∘ eA, ?_⟩
    · intro i j hij
      exact horder (eO.strictMono hij)
    · intro f
      obtain ⟨o, hp, hm⟩ := hrecord f
      refine ⟨e.symm o, ?_, ?_⟩
      · rw [hlabel]
        exact (isPivot_reindex M (Sum.elim oldLabel movableLabel) time e (test f) (e.symm o)).2
          (by simpa using hp)
      · cases o <;> simpa [occurrenceMark, e, m, Function.comp_def] using hm
  apply (Finset.card_le_card hsub).trans
  apply card_markedPivotPatterns_le M b a test m s hs
  intro o
  rw [hlabel]
  exact hground (e o)

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Blocks
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]

lemma blockTime_lt_iff (F : T → Set α) (τ : A → T) (x y : BlockOld F ⊕ A) :
    blockTime F τ x < blockTime F τ y ↔ blockKey F τ x < blockKey F τ y := by
  let := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  change (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm x <
    (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm y ↔ _
  exact OrderIso.lt_iff_lt _

lemma blockTime_injective (F : T → Set α) (τ : A → T) :
    Function.Injective (blockTime F τ) := by
  intro x y h
  apply blockKey_injective F τ
  apply le_antisymm <;> apply le_of_not_gt <;> intro hh
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ y x).2 hh))
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ x y).2 hh))

lemma blockTime_old_strictMono (F : T → Set α) (τ : A → T) :
    StrictMono (fun o : BlockOld F => blockTime F τ (Sum.inl o)) := by
  intro x y hxy
  apply (blockTime_lt_iff F τ _ _).2
  change toLex (blockOldStage (F := F) x, toLex ((blockOldLabel (α := α) (F := F) x : WithTop α), 0)) <
    toLex (blockOldStage (F := F) y, toLex ((blockOldLabel (α := α) (F := F) y : WithTop α), 0))
  have hh : x.val < y.val := hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hh with hs | ⟨hs, hl⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hs)
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hs,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (WithTop.coe_lt_coe.mpr hl))⟩)

lemma stage_lt_implies_blockTime_lt (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockStage F τ x < blockStage F τ y) :
    blockTime F τ x < blockTime F τ y := by
  apply (blockTime_lt_iff F τ _ _).2
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  cases x <;> cases y <;> exact h

lemma blockTime_le_implies_stage_le (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockTime F τ x ≤ blockTime F τ y) :
    blockStage F τ x ≤ blockStage F τ y := by
  by_contra hh
  exact (not_lt_of_ge h) (stage_lt_implies_blockTime_lt F τ (lt_of_not_ge hh))

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_BlockPatterns
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T] {n : ℕ}

lemma pivot_block_birth (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {o : BlockOld F ⊕ A}
    (hp : IsPivot M (blockLabel F a) (blockTime F τ) e o) :
    e ∈ M.closure (blockPrefix F a τ (blockStage F τ o)) ∧
      e ∉ M.closure (blockBefore F a τ (blockStage F τ o)) := by
  constructor
  · apply M.closure_subset_closure (Set.image_mono ?_) hp.1
    exact fun p h => blockTime_le_implies_stage_le F τ h
  · intro h
    apply hp.2
    apply M.closure_subset_closure (Set.image_mono ?_) h
    exact fun p h => stage_lt_implies_blockTime_lt F τ h

lemma block_birth_unique
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {k l : T}
    (hk : e ∈ M.closure (blockPrefix F a τ k) ∧ e ∉ M.closure (blockBefore F a τ k))
    (hl : e ∈ M.closure (blockPrefix F a τ l) ∧ e ∉ M.closure (blockBefore F a τ l)) :
    k = l := by
  rcases lt_trichotomy k l with h | rfl | h
  · exact (hl.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hk.1)).elim
  · rfl
  · exact (hk.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hl.1)).elim

lemma blockBirthPattern_mem_freeMarkedPatterns (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool)
    (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hspan : ∀ f, test f ∈ M.closure (Set.range (blockLabel F a))) :
    blockBirthPattern M F a τ test mark ∈
      freeMarkedPatterns M (blockOldLabel (F := F)) a test (fun o : BlockOld F => mark (blockOldStage (F := F) o)) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, blockTime F τ, blockTime_old_strictMono F τ,
    blockTime_injective F τ, mark ∘ τ, ?_⟩
  intro f
  obtain ⟨o, hp⟩ := exists_pivot M (blockLabel F a) (blockTime F τ) (hnonloop f) (hspan f)
  refine ⟨o, hp, ?_⟩
  have hb := pivot_block_birth M F a τ hp
  change Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o = true ↔ _
  have hm : Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o =
      mark (blockStage F τ o) := by cases o <;> rfl
  rw [hm]
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨blockStage F τ o, h, hb⟩
  · rintro ⟨k, hmark, hk⟩
    have heq := block_birth_unique M F a τ hb hk
    simpa only [heq] using hmark

lemma blockPrefix_eq
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (hF : Monotone F)
    (a : A → α) (τ : A → T) (k : T) :
    blockPrefix F a τ k = F k ∪ a '' {g | τ g ≤ k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (hF ho o.property)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · exact ⟨Sum.inl ⟨toLex (k, e), he⟩, by change k ≤ k; exact le_rfl, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

lemma blockBefore_eq_iUnion
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (a : A → α) (τ : A → T)
    (k : T) :
    blockBefore F a τ k = (⋃ j : T, ⋃ (_ : j < k), F j) ∪ a '' {g | τ g < k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (mem_iUnion.mpr ⟨blockOldStage (F := F) o, mem_iUnion.mpr ⟨ho, o.property⟩⟩)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · obtain ⟨j, hj, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      exact ⟨Sum.inl ⟨toLex (j, e), he⟩, hj, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Phases
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B]

lemma upperPath_mono
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α) (hF : Monotone F)
    (a : G → α) (θ : G → B) : Monotone (upperPath M F a θ) := by
  intro b c hbc
  exact M.closure_subset_closure (union_subset_union (hF hbc)
    (image_mono (fun _ hx => hx.trans hbc)))

lemma upperPath_subset_lowerPath
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α)
    (a : G → α) (θ : G → B) {b c : B} (hbc : b < c) :
    upperPath M F a θ b ⊆ lowerPath M F a θ c := by
  apply M.closure_subset_closure
  apply union_subset_union
  · exact fun e he => mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hbc, he⟩⟩
  · exact image_mono (fun _ hx => lt_of_le_of_lt hx hbc)

lemma phase_prefix_end_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      (F b ∪ a '' {g | θ g ≤ b}) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have hc : (ofLex (blockOldStage (F := phaseOld F K) o)).1 ≤ b := by
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact ht.elim le_of_lt (fun h => h.1.le)
      have hl : blockOldLabel (F := phaseOld F K) o ∈ F (ofLex (blockOldStage (F := phaseOld F K) o)).1 := by
        have hp := o.property
        change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      exact Or.inl (Or.inl (hF hc hl))
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inl (Or.inr ⟨g, ht.elim le_of_lt (fun h => h.1.le), rfl⟩)
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro ((he | ⟨g, hg, rfl⟩) | ⟨w, hw, rfl⟩)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, true), e), he⟩, ?_, rfl⟩
      change toLex (b, true) ≤ toLex (b, true)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hg).imp id (fun h => ⟨h, le_rfl⟩))
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, show (false : Bool) ≤ true from by decide⟩))

lemma phase_endpoint (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true))) =
      upperPath M F a θ b := by
  rw [phase_prefix_end_eq F K hF hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · exact M.subset_closure _ (by simp [hE])
    · rintro _ ⟨w, hw, rfl⟩
      exact upperPath_mono M F hF a θ hw (hz w)
  · exact M.closure_subset_closure subset_union_left

lemma phase_prefix_interior_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) =
      (((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b}) ∪ K b) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have ht := Prod.Lex.toLex_le_toLex.mp ho
      have hp := o.property
      change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
      rcases ht with hc | ⟨hc, hb⟩
      · left; left; left
        refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hc, ?_⟩⟩
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      · left; right
        have hf : (ofLex (blockOldStage (F := phaseOld F K) o)).2 = false := by
          change (ofLex (blockOldStage (F := phaseOld F K) o)).2 ≤ false at hb
          exact le_antisymm hb bot_le
        change (ofLex (blockOldStage (F := phaseOld F K) o)).1 = b at hc
        change blockOldLabel (F := phaseOld F K) o ∈ K b
        simpa [phaseOld, hf, hc] using hp
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        have hg : θ g < b := ht.elim id (fun h => by have hh : false = true := h.2 rfl; cases hh)
        exact Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro (((he | ⟨g, hg, rfl⟩) | hk) | ⟨w, hw, rfl⟩)
    · obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      refine ⟨Sum.inl ⟨toLex (toLex (c, true), e), he⟩, ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hc)
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hg)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, false), e), hk⟩, ?_, rfl⟩
      change toLex (b, false) ≤ toLex (b, false)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, le_rfl⟩))

lemma phase_interior (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false))) =
      M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  rw [phase_prefix_interior_eq F K hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    rintro e ((he | hk) | ⟨w, hw, rfl⟩)
    · apply M.subset_closure _ (by simp [hE])
      exact Or.inl (Or.inl (M.subset_closure _ (by simp [hE]) he))
    · exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inr hk))
    · rcases lt_or_eq_of_le hw with hw | hw
      · apply M.subset_closure _ (by simp [hE])
        exact Or.inl (Or.inl (upperPath_subset_lowerPath M F a θ hw (hz w)))
      · exact M.subset_closure _ (by simp [hE]) (Or.inr ⟨w, hw, rfl⟩)
  · rw [union_assoc (lowerPath M F a θ b), lowerPath, M.closure_union_closure_left_eq, ← union_assoc]
    apply M.closure_subset_closure
    exact union_subset_union Subset.rfl (image_mono (fun _ h => h.le))

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_PhasePattern
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B] {n : ℕ}

lemma lex_lt_true_iff_le_false
    {B : Type u_4} [Fintype B] [LinearOrder B] (p : B ×ₗ Bool) (b : B) :
    p < toLex (b, true) ↔ p ≤ toLex (b, false) := by
  rw [Prod.Lex.lt_iff, Prod.Lex.le_iff]
  cases (ofLex p).2 <;> simp

lemma phase_before_true
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (a : G → α) (z : Z → α)
    (θ : G → B) (β : Z → B) (b : B) :
    blockBefore (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) := by
  unfold blockBefore blockPrefix
  congr 1
  ext o
  exact lex_lt_true_iff_le_false _ _

lemma mem_phase_pattern (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) ↔
      ∃ b, test f ∈ upperPath M F a θ b ∧
        test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hafter, hbefore⟩
    change (ofLex p).2 = true at hp
    have hp' : p = toLex ((ofLex p).1, true) := congrArg toLex (Prod.ext rfl hp)
    rw [hp'] at hafter hbefore
    rw [phase_endpoint M hE F K hF hK a z θ β hz] at hafter
    rw [phase_before_true, phase_interior M hE F K hK a z θ β hz] at hbefore
    exact ⟨(ofLex p).1, hafter, hbefore⟩
  · rintro ⟨b, hafter, hbefore⟩
    refine ⟨toLex (b, true), rfl, ?_, ?_⟩
    · rwa [phase_endpoint M hE F K hF hK a z θ β hz]
    · rwa [phase_before_true, phase_interior M hE F K hK a z θ β hz]

lemma first_inter_phase_eq_residual (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α)
    (P : B → Finset (Fin n)) (first : Finset (Fin n))
    (hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ P b)
    (hP : ∀ b f, f ∈ P b → test f ∈ upperPath M F a θ b ∧ test f ∉ lowerPath M F a θ b) :
    first ∩ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) = residualOfLayers M F K a z θ β test P := by
  classical
  ext f
  rw [Finset.mem_inter, mem_phase_pattern M hE F K hF hK a z θ β hz]
  simp only [residualOfLayers, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hf, c, hc, hcnot⟩
    obtain ⟨b, hb⟩ := (hfirst f).1 hf
    have hpb := hP b f hb
    have hbc : b = c := by
      rcases lt_trichotomy b c with h | h | h
      · apply False.elim
        apply hcnot
        exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inl
          (upperPath_subset_lowerPath M F a θ h hpb.1)))
      · exact h
      · exact (hpb.2 (upperPath_subset_lowerPath M F a θ h hc)).elim
    exact ⟨b, hb, hbc.symm ▸ hcnot⟩
  · rintro ⟨b, hb, hnot⟩
    exact ⟨(hfirst f).2 ⟨b, hb⟩, b, (hP b f hb).1, hnot⟩

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_Entropy
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Finset

lemma binomialSum_le_weighted (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have htrunc : (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := by
    rw [binomialSum, Nat.cast_sum]
    apply (sum_subset inter_subset_left ?_).symm
    intro k hkd hnot
    have hnk : n < k := by simpa only [mem_inter, hkd, true_and, mem_Iic, not_le] using hnot
    simp [Nat.choose_eq_zero_of_lt hnk]
  have hp (k : ℕ) (hkd : k ≤ d) : 1 ≤ κ ^ d * (κ⁻¹) ^ k := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ (pow_pos hkpos k)).2 (pow_le_pow_right₀ hκ hkd)
  calc
    (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := htrunc
    _ ≤ ∑ k ∈ Iic d ∩ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (hp k (mem_Iic.mp (mem_inter.mp hk).1))
        (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ ∑ k ∈ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)
    _ = κ ^ d * (1 + κ⁻¹) ^ n := by
      rw [← mul_sum, add_comm 1, add_pow, Nat.range_succ_eq_Iic]
      simp

lemma binomialSum_le_exp (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hone : 1 + κ⁻¹ ≤ Real.exp κ⁻¹ := by simpa [add_comm] using Real.add_one_le_exp κ⁻¹
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + κ⁻¹) hone n
  calc
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := binomialSum_le_weighted n d κ hκ
    _ ≤ κ ^ d * (Real.exp κ⁻¹) ^ n := mul_le_mul_of_nonneg_left hpow (pow_nonneg hkpos.le d)
    _ = Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv, Real.exp_nat_mul]

lemma residual_raw_count_le_exp (n q : ℕ) (κ : ℝ) (hκ : 2 ≤ κ)
    (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have hkone : 1 ≤ κ := by linarith
  have hkpos : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log κ := Real.log_nonneg hkone
  have hloghalf : (1 : ℝ) / 2 ≤ Real.log κ := by
    have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) hκ)
  have h4 : (4 : ℝ) ^ (2 * q) ≤ Real.exp (((4 * q : ℕ) : ℝ) * Real.log κ) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
    calc
      (4 : ℝ) ^ (2 * q) = (2 : ℝ) ^ (4 * q) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
      _ ≤ κ ^ (4 * q) := pow_le_pow_left₀ (by norm_num) hκ _
  have hs := binomialSum_le_exp n q κ hkone
  have hs2 := binomialSum_le_exp n (2 * q) κ hkone
  have hproduct := mul_le_mul h4 hs2 (by positivity) (Real.exp_nonneg _)
  have hsquare := pow_le_pow_left₀ (by positivity) hs 2
  have hproductsquare := pow_le_pow_left₀ (by positivity) hproduct 2
  have hall := mul_le_mul hsquare hproductsquare (by positivity) (by positivity)
  have hexp : (((binomialSum n q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 : ℕ) : ℝ) ≤
      Real.exp (14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)) := by
    push_cast
    refine hall.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  apply hexp.trans (Real.exp_le_exp.mpr ?_)
  have hqlog := mul_le_mul_of_nonneg_right hq hlog
  have hn : (0 : ℝ) ≤ (n : ℝ) / κ := div_nonneg (Nat.cast_nonneg n) hkpos.le
  have hnlog : 4 * ((n : ℝ) / κ) ≤ 8 * ((n : ℝ) / κ) * Real.log κ := by
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hloghalf)]
  have hnlognonneg : 0 ≤ ((n : ℝ) / κ) * Real.log κ := mul_nonneg hn hlog
  calc
    14 * (q : ℝ) * Real.log κ + 4 * ((n : ℝ) / κ)
        ≤ 1000 * ((n : ℝ) / κ) * Real.log κ := by nlinarith
    _ = 1000 * Real.log κ / κ * n := by ring

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Pivots_ResidualFamily
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α O₁ O₂ : Type*} [Fintype α] [Fintype O₁] [LinearOrder O₁]
    [Fintype O₂] [LinearOrder O₂] {n : ℕ}

lemma mem_smallSubsets
    {α : Type u_1} [Fintype α] (U J : Finset α) (q : ℕ) :
    J ∈ smallSubsets U q ↔ J ⊆ U ∧ J.card ≤ q := by
  classical
  simp [smallSubsets]

lemma card_smallSubsets_le (U : Finset α) (q : ℕ) :
    (smallSubsets U q).card ≤ binomialSum U.card q := by
  classical
  have hsub : smallSubsets U q ⊆ (Finset.Iic q).biUnion (fun k => U.powersetCard k) := by
    intro J hJ
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    exact mem_biUnion.mpr ⟨J.card, mem_Iic.mpr hJq, mem_powersetCard.mpr ⟨hJU, rfl⟩⟩
  calc
    (smallSubsets U q).card ≤ ((Finset.Iic q).biUnion (fun k => U.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Iic q, (U.powersetCard k).card := card_biUnion_le
    _ = binomialSum U.card q := by simp [binomialSum]

lemma card_intersectionFamily_le (F G : Finset (Finset (Fin n))) :
    (intersectionFamily F G).card ≤ F.card * G.card := by
  exact card_image_le.trans_eq (card_product F G)

lemma mem_residualFamily (M : Matroid α) (U J Z : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (T₁ T₂ : Finset (Fin n))
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q)
    (hT₁ : T₁ ∈ freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
    (hT₂ : T₂ ∈ freeMarkedPatterns M old₂
      (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂) :
    T₁ ∩ T₂ ∈ residualFamily M U q old₁ old₂ mark₁ mark₂ test := by
  classical
  apply mem_biUnion.mpr
  refine ⟨J, (mem_smallSubsets U J q).2 ⟨hJ, hJq⟩, mem_biUnion.mpr ?_⟩
  refine ⟨Z, (mem_smallSubsets U Z q).2 ⟨hZ, hZq⟩, ?_⟩
  exact mem_image.mpr ⟨(T₁, T₂), mem_product.mpr ⟨hT₁, hT₂⟩, rfl⟩

lemma card_residualFamily_le (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E) :
    (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤
      (binomialSum U.card q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 := by
  classical
  let B := 4 ^ (2 * q) * binomialSum n (2 * q)
  let C := smallSubsets U q
  have hpair (J : Finset α) (hJ : J ∈ C) (Z : Finset α) (hZ : Z ∈ C) :
      (intersectionFamily
        (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
        (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card
        ≤ B ^ 2 := by
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    obtain ⟨hZU, hZq⟩ := (mem_smallSubsets U Z q).1 hZ
    have hfirst : (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₁ (fun a : J => a.val) test mark₁ (2 * q)
      · simpa using (show J.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₁ o
        | inr a => exact hU (hJU a.property)
    have hsecond : (freeMarkedPatterns M old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂ (2 * q)
      · simpa using (show J.card + Z.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₂ o
        | inr a =>
          cases a with
          | inl a => exact hU (hJU a.property)
          | inr a => exact hU (hZU a.property)
    exact (card_intersectionFamily_le _ _).trans ((Nat.mul_le_mul hfirst hsecond).trans_eq (pow_two B).symm)
  have hsum : (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤ C.card ^ 2 * B ^ 2 := by
    calc
      _ ≤ ∑ J ∈ C, ((C.biUnion fun Z => intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂))).card :=
        card_biUnion_le
      _ ≤ ∑ J ∈ C, ∑ Z ∈ C, (intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card :=
        sum_le_sum fun _ _ => card_biUnion_le
      _ ≤ ∑ _J ∈ C, ∑ _Z ∈ C, B ^ 2 := sum_le_sum fun J hJ => sum_le_sum fun Z hZ => hpair J hJ Z hZ
      _ = C.card ^ 2 * B ^ 2 := by simp [pow_two, Nat.mul_assoc]
  exact hsum.trans (Nat.mul_le_mul_right (B ^ 2) (Nat.pow_le_pow_left (card_smallSubsets_le U q) 2))

lemma card_residualFamily_le_exp (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E)
    (hn : U.card = n) (κ : ℝ) (hκ : 2 ≤ κ) (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have h := card_residualFamily_le M d U q old₁ old₂ mark₁ mark₂ test hU h₁ h₂
  rw [hn] at h
  exact (show ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      (((binomialSum n q)^2 * (4^(2*q) * binomialSum n (2*q))^2 : ℕ) : ℝ) by exact_mod_cast h).trans
    (residual_raw_count_le_exp n q κ hκ hq)

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Generators
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma monotone_set_timing
    {α : Type u_1} [Fintype α] (J : ℕ → Set α) (hJ : Monotone J) (N : ℕ) :
    ∃ τ : α → ℕ, ∀ j ≤ N, J j = {g | g ∈ J N ∧ τ g ≤ j} := by
  classical
  let hex := fun g (hg : g ∈ J N) => show ∃ j, g ∈ J j from ⟨N, hg⟩
  let τ := fun g => if hg : g ∈ J N then Nat.find (hex g hg) else 0
  refine ⟨τ, ?_⟩
  intro j hj
  ext g
  constructor
  · intro hg
    have hgN := hJ hj hg
    refine ⟨hgN, ?_⟩
    simpa [τ, hgN] using Nat.find_min' (hex g hgN) hg
  · rintro ⟨hgN, hτ⟩
    have hfind : Nat.find (hex g hgN) ≤ j := by simpa [τ, hgN] using hτ
    exact hJ hfind (Nat.find_spec (hex g hgN))

lemma nominalPath_timed_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧
      (∀ j ≤ pathHorizon h,
        M.closure (guardedPath M hE κ D C h (activation h + j) ∪
          {g | g ∈ G ∧ τ g ≤ j}) = nominalPath M hE κ D C h (activation h + j)) := by
  obtain ⟨G, hGD, hGcard, J, hJmono, hJG, hgen⟩ := nominalPath_generators M hE κ hκ D C h
  obtain ⟨τ, hτ⟩ := monotone_set_timing J hJmono (pathHorizon h)
  refine ⟨J (pathHorizon h), (hJG _ le_rfl).trans hGD, ?_, τ, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left κ (Set.ncard_mono (hJG _ le_rfl))).trans hGcard
  · intro g hg
    exact ((Set.ext_iff.mp (hτ _ le_rfl) g).mp hg).2
  · intro j hj
    rw [← hτ j hj]
    exact hgen j hj

lemma nominalPath_all_time_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧ ∀ k : ℤ,
        nominalPath M hE κ D C h k =
          M.closure (guardedPath M hE κ D C h k ∪ timedGeneratorSet G τ (activation h) k) := by
  obtain ⟨G, hGD, hGcard, τ, hbound, hgen⟩ := nominalPath_timed_generators M hE κ hκ D C h
  refine ⟨G, hGD, hGcard, τ, hbound, ?_⟩
  intro k
  by_cases hka : k < activation h
  · have hearly : k < -3 * (h : ℤ) - 1 := by
      dsimp [activation] at hka
      omega
    have hempty : timedGeneratorSet G τ (activation h) k = ∅ := by
      ext g
      simp only [timedGeneratorSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ htime
      omega
    rw [nominalPath_early M hE κ D C h hka, guardedPath_early M hE κ D C h hearly,
      hempty, union_empty, M.closure_closure]
  · by_cases hk0 : 0 ≤ k
    · rw [nominalPath_nonnegative M hE κ D C h hk0, guardedPath_nonnegative M hE κ D C h hk0]
      simp [M.closure_univ, hE]
    · let j := (k - activation h).toNat
      have hjcast : (j : ℤ) = k - activation h := Int.toNat_of_nonneg (by omega)
      have hj : j ≤ pathHorizon h := by
        have hhor := activation_add_horizon h
        omega
      have hkj : activation h + (j : ℤ) = k := by omega
      have hsets : {g | g ∈ G ∧ τ g ≤ j} = timedGeneratorSet G τ (activation h) k := by
        ext g
        simp only [timedGeneratorSet, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨hg, ht⟩ <;> exact ⟨hg, by omega⟩
      have h := hgen j hj
      rw [hkj, hsets] at h
      exact h.symm

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Timeline
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

lemma roundParity_le_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k ≤ b ↔ k ≤ b := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

lemma roundParity_lt_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k < b ↔ k ≤ b - 2 := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

variable {α G : Type*} [Fintype α] [LinearOrder α] [Fintype G]

lemma window_prefix (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockPrefix (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν k.val := by
  rw [blockPrefix_eq (fun t : IntWindow a => F t.val) (fun _ _ h => hF h)]
  rfl

lemma parity_upperPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    upperPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν b.val.val := by
  have hs : {i | parityPlacement a ε ν hν i ≤ b} = {i | ν i ≤ b.val.val} := by
    ext i
    exact roundParity_le_iff ε (ν i) b.val.val b.property
  unfold upperPath generatedPath
  rw [hs]

lemma parity_lowerPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    lowerPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν (b.val.val - 2) := by
  have hgen : g '' {i | parityPlacement a ε ν hν i < b} = g '' {i | ν i ≤ b.val.val - 2} := by
    congr 1
    ext i
    exact roundParity_lt_iff ε (ν i) b.val.val b.property
  unfold lowerPath generatedPath
  rw [hgen]
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    have hcb : c.val.val ≤ b.val.val - 2 := by
      have hb := b.property
      have hcmod := c.property
      change c.val.val < b.val.val at hc
      omega
    exact hF hcb he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ b.val.val - 2
      · let c : ParityWindow a ε := ⟨⟨b.val.val - 2, ⟨hlo, by have := b.val.property.2; omega⟩⟩,
          by change (b.val.val - 2) % 2 = (ε.val : ℤ); have := b.property; omega⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change b.val.val - 2 < b.val.val
        omega
      · have hearly : b.val.val - 2 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

lemma window_before (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockBefore (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν (k.val - 1) := by
  rw [blockBefore_eq_iUnion]
  have hgen : g '' {i | windowPlacement a ν hν i < k} = g '' {i | ν i ≤ k.val - 1} := by
    congr 1
    ext i
    change ν i < k.val ↔ ν i ≤ k.val - 1
    omega
  rw [hgen]
  unfold generatedPath
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    apply hF (show c.val ≤ k.val - 1 from by change c.val < k.val at hc; omega) he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ k.val - 1
      · let c : IntWindow a := ⟨k.val - 1, ⟨hlo, by have := k.property.2; omega⟩⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change k.val - 1 < k.val
        omega
      · have hearly : k.val - 1 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

end Pivots
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Encoding
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

lemma generatedPath_mono
    {α : Type u_1} [Fintype α] [LinearOrder α] {G : Type*}
    (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (g : G → α) (ν : G → ℤ) : Monotone (generatedPath M F g ν) := by
  intro k l hkl
  exact M.closure_subset_closure (union_subset_union (hF hkl)
    (image_mono (fun _ hx => hx.trans hkl)))

lemma first_integer_pattern {G : Type*} [Fintype G]
    (M : Matroid α) (hE : M.E = Set.univ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν)
      test (validBirthMark a ε) ↔
      ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hm, hx, hn⟩
    have hv : a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ) := by
      simpa [validBirthMark] using hm
    rw [window_prefix M F hF] at hx
    rw [window_before M hE F hF a hFe] at hn
    exact ⟨⟨k, hv.2.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1, hv.2.1, hx, hn⟩⟩
  · rintro ⟨b, hb⟩
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hb
    refine ⟨b.val, ?_, ?_, ?_⟩
    · simpa [validBirthMark] using And.intro hv.1 (And.intro hv.2.1 b.property)
    · rw [window_prefix M F hF]
      exact hv.2.2.1
    · rw [window_before M hE F hF a hFe]
      exact hv.2.2.2

lemma integerResidual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (U J Z : Finset α) (q : ℕ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (ha : a ≤ 0) (hFe : ∀ k < a, F k = M.closure ∅)
    (hFl : ∀ k, 0 ≤ k → F k = Set.univ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (hK : ∀ b, K b ⊆ F b.val.val)
    (ν : J → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0)
    (β : Z → ParityWindow a ε)
    (hz : ∀ w, w.val ∈ generatedPath M F (fun i : J => i.val) ν (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q) :
    integerResidual M (generatedPath M F (fun i : J => i.val) ν) test a ε K
        (fun w : Z => w.val) β ∈ integerResidualFamily M U q F a ε K test := by
  classical
  let g : J → α := fun i => i.val
  let z : Z → α := fun i => i.val
  let FW := fun t : IntWindow a => F t.val
  let FP := fun t : ParityWindow a ε => F t.val.val
  let θ := parityPlacement a ε ν hν
  let first := blockBirthPattern M FW g (windowPlacement a ν hν) test (validBirthMark a ε)
  let second := blockBirthPattern M (phaseOld FP K) (Sum.elim g z) (phasePlacement θ β) test
    (fun p => (ofLex p).2)
  have hz' : ∀ w, z w ∈ upperPath M FP g θ (β w) := by
    intro w
    rw [parity_upperPath]
    exact hz w
  have hFP : Monotone FP := fun _ _ h => hF h
  have hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b :=
    first_integer_pattern M hE F hF a hFe ε g ν hν test
  have hP : ∀ b f, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b →
      test f ∈ upperPath M FP g θ b ∧ test f ∉ lowerPath M FP g θ b := by
    intro b f hf
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hf
    rw [parity_upperPath, parity_lowerPath M hE F hF a hFe]
    exact ⟨hv.2.2.1, fun he => hv.2.2.2 (generatedPath_mono M F hF g ν (by omega) he)⟩
  have hinter := first_inter_phase_eq_residual M hE FP K hFP hK g z θ β hz' test
    (integerBirthLayer (generatedPath M F g ν) test a ε) first hfirst hP
  have hres : residualOfLayers M FP K g z θ β test
      (integerBirthLayer (generatedPath M F g ν) test a ε) =
      integerResidual M (generatedPath M F g ν) test a ε K z β := by
    ext f
    simp only [residualOfLayers, integerResidual, Finset.mem_filter, Finset.mem_univ, true_and,
      FP, θ, parity_lowerPath M hE F hF a hFe]
  rw [hres] at hinter
  rw [← hinter]
  apply mem_residualFamily M U J Z q _ _ _ _ test first second hJ hJq hZ hZq
  · apply blockBirthPattern_mem_freeMarkedPatterns M FW g (windowPlacement a ν hν) test
      (validBirthMark a ε) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let k : IntWindow a := ⟨0, by constructor <;> omega⟩
    have he : test f ∈ FW k := by change test f ∈ F 0; simp [hFl 0 le_rfl]
    exact ⟨Sum.inl ⟨toLex (k, test f), he⟩, rfl⟩
  · apply blockBirthPattern_mem_freeMarkedPatterns M (phaseOld FP K) (Sum.elim g z)
      (phasePlacement θ β) test (fun p => (ofLex p).2) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let b : ParityWindow a ε := ⟨⟨roundParity ε 0, by
      have := roundParity_bounds ε 0
      constructor <;> omega⟩, roundParity_mod ε 0⟩
    have he : test f ∈ phaseOld FP K (toLex (b, true)) := by
      change test f ∈ F (roundParity ε 0)
      simp [hFl _ (roundParity_bounds ε 0).1]
    exact ⟨Sum.inl ⟨toLex (toLex (b, true), test f), he⟩, rfl⟩

end MatroidProphet.Pivots

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Nominal
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

lemma nominal_residual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ)
    (U Z : Finset α) (hDU : D h ⊆ (U : Set α)) (hZU : Z ⊆ U)
    (hZcard : Z.card ≤ U.card / κ) (ε : Fin 2)
    (K : ParityWindow (activation h) ε → Set α)
    (hK : ∀ b, K b ⊆ guardedPath M hE κ D C h b.val.val)
    (β : Z → ParityWindow (activation h) ε)
    (hz : ∀ w, w.val ∈ nominalPath M hE κ D C h (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅) :
    integerResidual M (nominalPath M hE κ D C h) test (activation h) ε K
        (fun w : Z => w.val) β ∈
      integerResidualFamily M U (U.card / κ) (guardedPath M hE κ D C h)
        (activation h) ε K test := by
  classical
  obtain ⟨G, hGD, hGcard, τ, hτ, hgen⟩ := nominalPath_all_time_generators M hE κ hκ D C h
  let J : Finset α := G.toFinset
  let ν : J → ℤ := fun i => activation h + (τ i.val : ℤ)
  have hJ : J ⊆ U := by
    intro e he
    exact hDU (hGD (Set.mem_toFinset.mp he))
  have hJcard : J.card ≤ U.card / κ := by
    apply (Nat.le_div_iff_mul_le hκ).2
    have hDUcard : (D h).ncard ≤ U.card := by simpa using Set.ncard_mono hDU
    have hcard : κ * J.card ≤ U.card := by
      simpa only [J, ← Set.ncard_eq_toFinset_card'] using hGcard.trans hDUcard
    simpa only [Nat.mul_comm] using hcard
  have hν : ∀ i, activation h ≤ ν i ∧ ν i ≤ 0 := by
    intro i
    have hτi := hτ i.val (Set.mem_toFinset.mp i.property)
    have hhor := activation_add_horizon h
    dsimp [ν]
    constructor <;> omega
  have hX : nominalPath M hE κ D C h = generatedPath M (guardedPath M hE κ D C h)
      (fun i : J => i.val) ν := by
    funext k
    rw [hgen k]
    unfold generatedPath
    congr 1
    congr 1
    ext e
    constructor
    · rintro ⟨he, ht⟩
      exact ⟨⟨e, Set.mem_toFinset.mpr he⟩, ht, rfl⟩
    · rintro ⟨i, ht, rfl⟩
      exact ⟨Set.mem_toFinset.mp i.property, ht⟩
  rw [hX] at hz ⊢
  apply integerResidual_mem_family M hE U J Z (U.card / κ)
    (guardedPath M hE κ D C h) (guardedPath_mono M hE κ D C h)
    (activation h) (by unfold activation; omega) _
    (fun k hk => guardedPath_nonnegative M hE κ D C h hk) ε K hK ν hν β hz test hnonloop hJ hJcard hZU hZcard
  intro k hk
  apply guardedPath_early M hE κ D C h
  unfold activation at hk
  omega

lemma integerResidualFamily_card_le_exp (M : Matroid α) (hE : M.E = Set.univ) (d : α)
    (U : Finset α) (κ : ℕ) (hκ : 2 ≤ κ) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (test : Fin n → α) (hn : U.card = n) :
    ((integerResidualFamily M U (U.card / κ) F a ε K test).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * n) := by
  apply card_residualFamily_le_exp M d U (U.card / κ) _ _ _ _ test
    (by simp [hE]) (by simp [hE]) (by simp [hE]) hn (κ : ℝ) (by exact_mod_cast hκ)
  have hkpos : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  apply (le_div_iff₀ hkpos).2
  rw [← hn]
  exact_mod_cast Nat.div_mul_le_self U.card κ

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Comparison
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma natRank_union_le_add_ncard (M : Matroid α) (X Z : Set α) :
    natRank M (X ∪ Z) ≤ natRank M X + Z.ncard := by
  have hz : Z.encard ≠ ⊤ := (Set.toFinite Z).encard_lt_top.ne
  have h := ENat.toNat_le_toNat (M.eRk_union_le_eRk_add_encard X Z)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, hz⟩)
  simpa only [ENat.toNat_add (rank_ne_top M X) hz, natRank, Set.ncard_def] using h

lemma densityExpansion_residual_le_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard ≤ κ * Z.ncard := by
  dsimp only
  have hd := densityExpansion_residual M hE κ D P Z
  have hr := Nat.mul_le_mul_left κ
    (natRank_union_le_add_ncard M (densityExpansion M hE κ D P) Z)
  rw [Nat.mul_add] at hr
  dsimp only at hd
  omega

lemma safe_layer_le_witness_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D F K Z A S : Set α)
    (hS : S ⊆ (D ∩ A) \ densityExpansion M hE κ D (F ∪ K)) :
    S.ncard ≤ κ * Z.ncard +
      (A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)).ncard := by
  let Q := densityExpansion M hE κ D (F ∪ K)
  let R := A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)
  have hX : densityExpansion M hE κ D F ⊆ Q :=
    densityExpansion_mono M hE κ D subset_union_left
  have hK : K ⊆ Q := subset_union_right.trans
    (densityExpansion_extensive M hE κ D (F ∪ K))
  have hcl : M.closure (densityExpansion M hE κ D F ∪ K ∪ Z) ⊆
      M.closure (Q ∪ Z) :=
    M.closure_subset_closure (union_subset_union (union_subset hX hK) Subset.rfl)
  have hcharge : S \ R ⊆ D ∩ (M.closure (Q ∪ Z) \ Q) := by
    intro e he
    have hs := hS he.1
    refine ⟨hs.1.1, hcl ?_, hs.2⟩
    by_contra hn
    exact he.2 ⟨hs.1.2, hn⟩
  have hcount := (Set.ncard_mono hcharge).trans
    (densityExpansion_residual_le_generators M hE κ D (F ∪ K) Z)
  exact (Set.ncard_le_ncard_sdiff_add_ncard S R).trans (Nat.add_le_add_right hcount _)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Constants
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

lemma residual_tail_coefficient :
    (1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) *
      densityThreshold ≤ -(26 * Real.log 2) := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold densityThreshold residualDelta
  rw [Real.log_pow]
  norm_num
  nlinarith

theorem residual_tail_constant (n : ℝ) (hn : densityThreshold ≤ n) :
    Real.exp ((1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) * n)
      ≤ residualDelta := by
  have hk : 0 < densityThreshold := constants_positive.2.1
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc := residual_tail_coefficient
  have hneg : 1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2 ≤ 0 := by
    nlinarith
  have hmul := mul_le_mul_of_nonpos_left hn hneg
  have he := Real.exp_le_exp.mpr (hmul.trans hc)
  have hid : Real.exp (-(26 * Real.log (2 : ℝ))) = residualDelta := by
    rw [Real.exp_neg]
    have hpow := Real.exp_nat_mul (Real.log (2 : ℝ)) 26
    norm_num at hpow
    rw [hpow]
    rw [Real.exp_log (by norm_num)]
    rfl
  rwa [hid] at he

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Probability
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_contains (q : α → ℝ) (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = ∏ e ∈ R, q e := by
  induction V using Finset.induction_on generalizing R with
  | empty =>
    have h : R = ∅ := Finset.subset_empty.mp hR
    subst R
    simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    by_cases heR : e ∈ R
    · have hRV : R.erase e ⊆ V := by
        intro x hx
        have hm := hR (mem_of_mem_erase hx)
        rcases mem_insert.mp hm with rfl | hm
        · exact (notMem_erase _ _ hx).elim
        · exact hm
      have hzero : bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = 0 := by
        conv_rhs => rw [← bitsExpectation_const q V 0]
        apply bitsExpectation_congr
        intro S hS
        have hn : ¬ R ⊆ S := fun hh => he (hS (hh heR))
        simp [hn]
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R.erase e ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R.erase e ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
          · intro h x hx
            by_cases hxe : x = e
            · simp [hxe]
            · exact mem_insert_of_mem (h (mem_erase.mpr ⟨hxe, hx⟩))
        simp only [hiff]
      rw [hzero, hyes, ih _ hRV]
      simpa using (mul_prod_erase R q heR)
    · have hRV : R ⊆ V := by
        intro x hx
        exact (mem_insert.mp (hR hx)).resolve_left (fun h => heR (h ▸ hx))
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h hx)).resolve_left (fun h => heR (h ▸ hx))
          · exact fun h => h.trans (subset_insert e S)
        simp only [hiff]
      rw [hyes, ih _ hRV]
      ring

lemma bitsExpectation_mul_const (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_contains_le_half_pow (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) ≤ (1 / 2 : ℝ) ^ R.card := by
  rw [bitsExpectation_contains q V R hR]
  simpa using prod_le_prod (fun e _ => hq0 e) (fun e _ => hqhalf e)

lemma residualBad_indicator_le (F : Finset (Finset α)) (t : ℝ) (S : Finset α) :
    residualBadIndicator F t S ≤
      ∑ R ∈ F, if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0 := by
  classical
  unfold residualBadIndicator
  split_ifs with hb
  · obtain ⟨R, hRF, hRt, hRS⟩ := hb
    have h := single_le_sum (f := fun R : Finset α =>
      if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0)
      (fun R _ => by split_ifs <;> norm_num) hRF
    simpa [hRt, hRS] using h
  · exact sum_nonneg (fun R _ => by split_ifs <;> norm_num)

lemma bitsExpectation_residualBad_le (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V) (t : ℝ) :
    bitsExpectation q V (fun S => residualBadIndicator F t S) ≤
      (F.card : ℝ) * Real.exp (-t * Real.log 2) := by
  classical
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqhalf e).trans (by norm_num)
  calc
    _ ≤ bitsExpectation q V (fun S => ∑ R ∈ F,
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) :=
      bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBad_indicator_le F t S)
    _ = ∑ R ∈ F, bitsExpectation q V (fun S =>
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) := bitsExpectation_sum q V F _
    _ ≤ ∑ _R ∈ F, Real.exp (-t * Real.log 2) := by
      apply sum_le_sum
      intro R hRF
      by_cases hRt : t < (R.card : ℝ)
      · simp only [hRt, ite_true]
        apply (bitsExpectation_contains_le_half_pow q hq0 hqhalf V R (hF R hRF)).trans
        have heq : (1 / 2 : ℝ) ^ R.card = Real.exp (-(R.card : ℝ) * Real.log 2) := by
          rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
          simp
        rw [heq]
        apply Real.exp_le_exp.mpr
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact mul_le_mul_of_nonneg_right (by linarith) hlog
      · simp only [hRt, ite_false, bitsExpectation_const]
        exact Real.exp_nonneg _
    _ = _ := by simp

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_MaskUnion
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_union (p q : α → ℝ) (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) =
      bitsExpectation (fun e => p e + (1 - p e) * q e) V f := by
  induction V using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert p V e he,
      bitsExpectation_insert (fun e => p e + (1 - p e) * q e) V e he]
    have hno : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (D ∪ C))) =
        (1 - q e) * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (D ∪ C))) +
        q e * bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      simp_rw [bitsExpectation_insert q V e he, union_insert]
      rw [bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_mul_const]
    have hyes : bitsExpectation p V (fun D => bitsExpectation q (insert e V) (fun C => f (insert e D ∪ C))) =
        bitsExpectation p V (fun D => bitsExpectation q V (fun C => f (insert e (D ∪ C)))) := by
      apply bitsExpectation_congr
      intro D hD
      rw [bitsExpectation_insert q V e he]
      simp only [insert_union, union_insert, insert_idem]
      ring
    rw [hno, hyes, ih f, ih (fun S => f (insert e S))]
    ring

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Tail
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma residualDelta_nonneg : 0 ≤ residualDelta := by unfold residualDelta; positivity

lemma bitsExpectation_residualBad_delta (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤ residualDelta := by
  have htail := bitsExpectation_residualBad_le q hq0 hqhalf V F hF (residualDelta * V.card)
  have hmul := mul_le_mul_of_nonneg_right hcard
    (Real.exp_nonneg (-(residualDelta * V.card) * Real.log 2))
  apply htail.trans (hmul.trans ?_)
  rw [← Real.exp_add]
  convert residual_tail_constant (V.card : ℝ) hn using 1
  congr 1
  ring

lemma capturedResidual_le
    {α : Type u_1} [DecidableEq α] (V S R : Finset α) (F : Finset (Finset α))
    (hS : S ⊆ V) (hR : R ∈ F) (hRS : R ⊆ S) :
    (R.card : ℝ) ≤ residualDelta * V.card +
      (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) S := by
  classical
  have hcard : (R.card : ℝ) ≤ V.card := by exact_mod_cast Finset.card_le_card (hRS.trans hS)
  have hδ : 0 ≤ residualDelta * (V.card : ℝ) := mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _)
  by_cases hsmall : (R.card : ℝ) ≤ residualDelta * V.card
  · have hind : 0 ≤ residualBadIndicator F (residualDelta * V.card) S := by
      unfold residualBadIndicator
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg V.card) hind]
  · have hbad : residualBad F (residualDelta * V.card) S := ⟨R, hR, lt_of_not_ge hsmall, hRS⟩
    simp only [residualBadIndicator, hbad, ite_true, mul_one]
    linarith

lemma tripleMask_residual_error_le
    (p q r : α → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (hpq : ∀ e, p e + (1 - p e) * q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ))
    (error : Finset α → Finset α → Finset α → ℝ)
    (herror : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V,
      error D C T ≤ residualDelta * V.card + (V.card : ℝ) *
        residualBadIndicator F (residualDelta * V.card) (D ∪ C)) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (error D C))) ≤
      2 * residualDelta * V.card := by
  have hpq0 : ∀ e, 0 ≤ p e + (1 - p e) * q e := by
    intro e
    exact add_nonneg (hp0 e) (mul_nonneg (sub_nonneg.mpr (hp1 e)) (hq0 e))
  have hbad := bitsExpectation_residualBad_delta (fun e => p e + (1 - p e) * q e)
    hpq0 hpq V F hF hcard hn
  calc
    _ ≤ bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (fun _T =>
          residualDelta * V.card + (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) (D ∪ C)))) := by
      apply bitsExpectation_mono p hp0 hp1
      intro D hD
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      exact bitsExpectation_mono r hr0 hr1 V (fun T hT => herror D hD C hC T hT)
    _ = residualDelta * V.card + (V.card : ℝ) * bitsExpectation
        (fun e => p e + (1 - p e) * q e) V (residualBadIndicator F (residualDelta * V.card)) := by
      simp_rw [bitsExpectation_const, bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
      rw [bitsExpectation_union]
    _ ≤ residualDelta * V.card + (V.card : ℝ) * residualDelta :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg V.card))
    _ = _ := by ring

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Transfer
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_mono (p q r : α → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (V : Finset α) {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T ≤ g D C T) :
    tripleMaskExpectation p q r V f ≤ tripleMaskExpectation p q r V g := by
  apply bitsExpectation_mono p hp0 hp1
  intro D hD
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  exact bitsExpectation_mono r hr0 hr1 V (fun T hT => h D hD C hC T hT)

lemma tripleMaskExpectation_add (p q r : α → ℝ) (V : Finset α)
    (f g : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => f D C T + g D C T) =
      tripleMaskExpectation p q r V f + tripleMaskExpectation p q r V g := by
  simp only [tripleMaskExpectation, bitsExpectation_add]

lemma tripleMaskExpectation_mul (p q r : α → ℝ) (V : Finset α) (c : ℝ)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V (fun D C T => c * f D C T) =
      c * tripleMaskExpectation p q r V f := by
  simp only [tripleMaskExpectation, bitsExpectation_mul_const]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Statistics
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α]

lemma nominalLayerSet_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2)
    (b : ParityWindow (activation h) ε) : nominalLayerSet M hE κ D C h U ε b ⊆ U :=
  fun _ he => he.1

lemma nominalLayerSet_disjoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (U : Set α) (ε : Fin 2) :
    Pairwise (fun b c => Disjoint (nominalLayerSet M hE κ D C h U ε b)
      (nominalLayerSet M hE κ D C h U ε c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro e hb hc
  have hval : b.val.val ≠ c.val.val := by
    intro heq
    exact hbc (Subtype.ext (Subtype.ext heq))
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact hc.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hb.2.2.2.1)
  · exact hb.2.2.2.2 (nominalPath_mono M hE κ D C h (by omega) hc.2.2.2.1)

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_GroupConditioning
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma trueGroup_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (trueGroup M d s i) (trueGroup M d s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro e hei hej
  exact hij (Option.some.inj (((mem_trueGroup M d s i e).mp hei).2.symm.trans
    ((mem_trueGroup M d s j e).mp hej).2))

lemma trueGroup_disjoint_H (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) : Disjoint (trueGroup M d s i) d.H := by
  apply disjoint_left.mpr
  intro e he hh
  exact ((mem_trueGroup M d s i e).mp he).1.2.1 hh

lemma mem_listed_iff (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    i ∈ listed M d s ↔ ∃ e ∈ d.D, e ∈ trueGroup M d s i := by
  simp only [listed, mem_biUnion, mem_trueGroup]
  constructor
  · rintro ⟨e, he, hi⟩
    by_cases hc : candidate M d s e (s e)
    · simp only [ite_eq_left hc, Option.mem_toFinset] at hi
      exact ⟨e, he, hc, hi⟩
    · simp only [ite_eq_right hc, Finset.notMem_empty] at hi
  · rintro ⟨e, he, hc, hi⟩
    exact ⟨e, he, by rw [ite_eq_left hc]; simp [hi]⟩

lemma listed_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    listed M (focalMasks d (trueGroup M d s i) A B C) s =
      (listed M d s \ {i}) ∪ (if A.Nonempty then {i} else ∅) := by
  ext j
  rw [mem_listed_iff]
  simp only [focalMasks, mem_union, mem_sdiff,
    mem_singleton, mem_listed_iff]
  by_cases hne : A.Nonempty
  · simp only [ite_eq_left hne, mem_singleton]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine Or.inl ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact Or.inr (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp (hA he)).2))
    · rintro (⟨⟨e, heD, hej⟩, hji⟩ | rfl)
      · refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
        intro hei
        exact hji (Option.some.inj
          (((mem_trueGroup M d s j e).mp hej).2.symm.trans
            ((mem_trueGroup M d s i e).mp hei).2))
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, Or.inr he, hA he⟩
  · simp only [ite_eq_right hne, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨e, he | he, hej⟩
      · refine ⟨⟨e, he.1, hej⟩, ?_⟩
        intro hji
        exact he.2 (hji ▸ hej)
      · exact False.elim (hne ⟨e, he⟩)
    · rintro ⟨⟨e, heD, hej⟩, hji⟩
      refine ⟨e, Or.inl ⟨heD, ?_⟩, hej⟩
      intro hei
      exact hji (Option.some.inj
        (((mem_trueGroup M d s j e).mp hej).2.symm.trans
          ((mem_trueGroup M d s i e).mp hei).2))

lemma groups_focalMasks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    groups M (focalMasks d (trueGroup M d s i) A B C) s =
      groups M (focalReference M d s i) s := by
  have hU : (trueGroup M d s i).Nonempty := hne.mono hA
  unfold groups focalReference
  rw [listed_focalMasks M d s i A B C hA,
    listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hne, ite_eq_left hU]

lemma focal_mem_reference_groups (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (hU : (trueGroup M d s i).Nonempty) :
    i ∈ groups M (focalReference M d s i) s := by
  rw [mem_groups]
  unfold focalReference
  rw [listed_focalMasks M d s i _ ∅ ∅ Subset.rfl, ite_eq_left hU]
  exact mem_union_right _ (mem_singleton_self i)

lemma groupMask_at_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) (i : ℤ)
    (hi : (groups M d s)[h]? = some i) :
    groupMask M d s mask h = ((mask ∩ trueGroup M d s i : Finset (Fin n)) : Set (Fin n)) := by
  ext e
  simp only [groupMask, Set.mem_ofPred_eq, Finset.mem_coe, mem_inter, mem_trueGroup, hi]

lemma replaceMask_inter_self (X U A : Finset (Fin n)) (hA : A ⊆ U) :
    ((X \ U) ∪ A) ∩ U = A := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heU⟩
    · exact False.elim (he.2 heU)
    · exact he
  · intro he
    exact ⟨Or.inr he, hA he⟩

lemma replaceMask_inter_other (X U A V : Finset (Fin n))
    (hA : A ⊆ U) (hUV : Disjoint U V) :
    ((X \ U) ∪ A) ∩ V = X ∩ V := by
  ext e
  simp only [mem_inter, mem_union, mem_sdiff]
  constructor
  · rintro ⟨he | he, heV⟩
    · exact ⟨he.1, heV⟩
    · exact False.elim (disjoint_left.mp hUV (hA he) heV)
  · rintro ⟨heX, heV⟩
    exact ⟨Or.inl ⟨heX, fun heU => disjoint_left.mp hUV heU heV⟩, heV⟩

lemma focal_group_key (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    (groups M (focalMasks d (trueGroup M d s i) A B C) s)[focalIndex M d s i]? = some i := by
  rw [groups_focalMasks M d s i A B C hA hne]
  exact groups_get?_idxOf M _ s i (focal_mem_reference_groups M d s i (hne.mono hA))

lemma focal_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) (focalIndex M d s i) = (Y : Set (Fin n)) := by
  rw [groupMask_at_key M _ s _ _ i (focal_group_key M d s i A B C hA hne),
    trueGroup_focalMasks, replaceMask_inter_self X _ Y hY]

lemma lower_group_mask (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C X Y Z : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (hY : Y ⊆ trueGroup M d s i) (hZ : Z ⊆ trueGroup M d s i)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    groupMask M (focalMasks d (trueGroup M d s i) A B C) s
      ((X \ trueGroup M d s i) ∪ Y) j =
    groupMask M (focalReference M d s i) s
      ((X \ trueGroup M d s i) ∪ Z) j := by
  have hi := groups_get?_idxOf M (focalReference M d s i) s i
    (focal_mem_reference_groups M d s i (hne.mono hA))
  obtain ⟨k, hk, hki⟩ := groups_earlier_key M (focalReference M d s i) s hi hj
  have hk' : (groups M (focalMasks d (trueGroup M d s i) A B C) s)[j]? = some k := by
    rwa [groups_focalMasks M d s i A B C hA hne]
  have hdisj := trueGroup_disjoint M d s (ne_of_gt hki)
  rw [groupMask_at_key M _ s _ j k hk', groupMask_at_key M _ s _ j k hk]
  simp only [focalReference, trueGroup_focalMasks]
  rw [replaceMask_inter_other X _ Y _ hY hdisj,
    replaceMask_inter_other X _ Z _ hZ hdisj]

end MatroidProphet.MainAlgorithm

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

lemma guardedPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    guardedPath M hE κ D C h k = guardedPath M hE κ D' C' h k := by
  induction h generalizing k with
  | zero => rfl
  | succ h ih =>
    simp only [guardedPath, hD h (Nat.lt_succ_self h), hC h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

lemma nominalPath_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C D' C' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j ≤ h, D j = D' j) (hC : ∀ j < h, C j = C' j) (k : ℤ) :
    nominalPath M hE κ D C h k = nominalPath M hE κ D' C' h k := by
  rw [nominalPath, nominalPath, hD h le_rfl,
    guardedPath_congr_prefix M hE κ D C D' C' h (fun j hj => hD j hj.le) hC k]

lemma lowerCompetition_congr_prefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T D' C' T' : ℕ → Set α) (h : ℕ)
    (hD : ∀ j < h, D j = D' j) (hC : ∀ j < h, C j = C' j)
    (hT : ∀ j < h, T j = T' j) (k : ℤ) :
    lowerCompetition M hE κ D C T k h = lowerCompetition M hE κ D' C' T' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [lowerCompetition, lowerCompetition, hT h (Nat.lt_succ_self h),
      ih (fun j hj => hD j (Nat.lt_succ_of_lt hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))
        (fun j hj => hT j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj)),
      nominalPath_congr_prefix M hE κ D C D' C' h
        (fun j hj => hD j (Nat.lt_succ_of_le hj)) (fun j hj => hC j (Nat.lt_succ_of_lt hj))]

namespace MainAlgorithm
open Finset
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma focal_prefix_masks (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty)
    (j : ℕ) (hj : j < focalIndex M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    groupMask M f s f.D j = groupMask M r s r.D j ∧
    groupMask M f s f.C j = groupMask M r s r.C j ∧
    groupMask M f s f.T j = groupMask M r s r.T j := by
  exact ⟨lower_group_mask M d s i A B C d.D A _ hA hne hA Finset.Subset.rfl j hj,
    lower_group_mask M d s i A B C d.C B ∅ hA hne hB (empty_subset _) j hj,
    lower_group_mask M d s i A B C d.T C ∅ hA hne hC (empty_subset _) j hj⟩

lemma focal_incoming_path (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    guardedPath M hE κ (groupMask M f s f.D) (groupMask M f s f.C) (focalIndex M d s i) k =
      guardedPath M hE κ (groupMask M r s r.D) (groupMask M r s r.C) (focalIndex M d s i) k := by
  apply guardedPath_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1

lemma focal_lowerCompetition (M : Matroid (Fin n)) (hE : M.E = Set.univ) (κ : ℕ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) (hne : A.Nonempty) (k : ℤ) :
    let f := focalMasks d (trueGroup M d s i) A B C
    let r := focalReference M d s i
    lowerCompetition M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) k (focalIndex M d s i) =
      lowerCompetition M hE κ (groupMask M r s r.D) (groupMask M r s r.C)
        (groupMask M r s r.T) k (focalIndex M d s i) := by
  apply lowerCompetition_congr_prefix
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.1
  · exact fun j hj => (focal_prefix_masks M d s i A B C hA hB hC hne j hj).2.2

lemma focal_observed_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i) :
    let f := focalMasks d (trueGroup M d s i) A B C
    (f.H ∪ f.D ∪ f.C) ∩ trueGroup M d s i = A ∪ B := by
  dsimp only [focalMasks]
  rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
    disjoint_iff_inter_eq_empty.mp (trueGroup_disjoint_H M d s i).symm,
    replaceMask_inter_self _ _ _ hA, replaceMask_inter_self _ _ _ hB, Finset.empty_union]

lemma focal_listed_iff_nonempty (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) :
    i ∈ groups M (focalMasks d (trueGroup M d s i) A B C) s ↔ A.Nonempty := by
  rw [mem_groups, listed_focalMasks M d s i A B C hA]
  by_cases hne : A.Nonempty <;> simp [hne]

lemma listedSafeStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2) :
    listedSafeStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i Y ε = 0 := by
  rw [listedSafeStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedRankStatistic_focal_empty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (B C : Finset (Fin n)) (ε : Fin 2) :
    listedRankStatistic M hE κ (focalMasks d (trueGroup M d s i) ∅ B C) s i ε = 0 := by
  rw [listedRankStatistic, ite_eq_right]
  simp only [focal_listed_iff_nonempty M d s i ∅ B C (Finset.empty_subset _),
    Finset.not_nonempty_empty, not_false_eq_true]

lemma listedSafeStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (Y : Set (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedSafeStatistic M hE κ f s i Y ε =
      safeLayerStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.D : Set (Fin n)) ∩ Y) ε := by
  dsimp only
  rw [listedSafeStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma listedRankStatistic_focal_nonempty (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (A B C : Finset (Fin n)) (ε : Fin 2)
    (hA : A ⊆ trueGroup M d s i) (hne : A.Nonempty) :
    let f := focalMasks d (trueGroup M d s i) A B C
    listedRankStatistic M hE κ f s i ε =
      nominalRankStatistic M hE κ (groupMask M f s f.D) (groupMask M f s f.C)
        (groupMask M f s f.T) (focalIndex M d s i) (trueGroup M d s i : Set (Fin n))
        ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ε := by
  dsimp only
  rw [listedRankStatistic, ite_eq_left ((focal_listed_iff_nonempty M d s i A B C hA).mpr hne),
    groups_focalMasks M d s i A B C hA hne, trueGroup_focalMasks]
  rfl

lemma focal_density_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) (A B C : Finset (Fin n))
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n))) :
    ((focalMasks d (trueGroup M d s i) A B C).D : Set (Fin n)) ∩ Y =
      (A : Set (Fin n)) ∩ Y := by
  ext e
  simp only [Set.mem_inter_iff, Finset.mem_coe, focalMasks, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨he | he, heY⟩
    · exact False.elim (he.2 (hY heY))
    · exact ⟨he, heY⟩
  · rintro ⟨heA, heY⟩
    exact ⟨Or.inr heA, heY⟩

end MainAlgorithm
end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_PathRankCost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma lowerCompetition_subset_guarded (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    lowerCompetition M hE κ D C T b h ⊆ guardedPath M hE κ D C h b := by
  induction h with
  | zero => exact Set.empty_subset _
  | succ h ih =>
    apply Set.union_subset
    · exact ih.trans ((guarded_subset_nominal M hE κ D C h b).trans
        (nominal_subset_guarded M hE κ D C h b))
    · exact fun _ he => nominal_subset_guarded M hE κ D C h b he.2.1

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Witnesses
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α B : Type*} [Fintype α] [Fintype B]

lemma exists_rankWitness (M : Matroid α) (hE : M.E = Set.univ) (A S : Set α) :
    ∃ Z : Set α, Z ⊆ S ∧ Z.ncard = conditionalRank M S A ∧ S ⊆ M.closure (A ∪ Z) := by
  obtain ⟨Z, hZ, hgen, hcard⟩ := exists_extension_generators M hE (M.closure A) S
    (M.closure (M.closure A ∪ S)) (Matroid.isFlat_closure (M := M) _) rfl
  refine ⟨Z, hZ.trans sdiff_subset, ?_, ?_⟩
  · simp only [natRank_closure] at hcard
    have hrank : natRank M (M.closure A ∪ S) = natRank M (A ∪ S) := by
      simp only [natRank, M.eRk_union_closure_left_eq]
    rw [hrank] at hcard
    have hr := conditionalRank_add_base M S A
    rw [union_comm S A] at hr
    omega
  · rw [M.closure_union_closure_left_eq, M.closure_union_closure_left_eq] at hgen
    rw [hgen]
    exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

lemma collect_disjoint_witnesses (W : B → Set α) (U : Finset α)
    (hW : ∀ b, W b ⊆ (U : Set α))
    (hdisj : Pairwise (fun b c => Disjoint (W b) (W c))) :
    ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ ∑ b, (W b).ncard ∧
      ∃ β : Z → B, ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  let Z := (⋃ b, W b).toFinset
  have hmem (w : Z) : ∃ b, w.val ∈ W b := by
    exact mem_iUnion.mp (Set.mem_toFinset.mp w.property)
  let β : Z → B := fun w => (hmem w).choose
  have hβ (w : Z) : w.val ∈ W (β w) := (hmem w).choose_spec
  refine ⟨Z, ?_, ?_, β, ?_⟩
  · intro e he
    obtain ⟨b, hb⟩ := mem_iUnion.mp (Set.mem_toFinset.mp he)
    exact hW b hb
  · rw [show Z.card = (⋃ b, W b).ncard from (Set.ncard_eq_toFinset_card' _).symm]
    exact Set.ncard_iUnion_le_of_fintype W
  · intro b
    ext e
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hw]
      exact hβ w
    · intro he
      let w : Z := ⟨e, Set.mem_toFinset.mpr (mem_iUnion.mpr ⟨b, he⟩)⟩
      have heq : β w = b := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) (hβ w) he
      exact ⟨w, heq, rfl⟩

lemma residualUnion_subset_mask
    {α : Type u_1} {B : Type u_2} [Fintype α] [Fintype B]
    (M : Matroid α) (P A W : B → Set α) (O : Set α)
    (hspan : ∀ b, P b \ O ⊆ M.closure (A b ∪ W b)) :
    (⋃ b, P b \ M.closure (A b ∪ W b)) ⊆ O := by
  intro e he
  obtain ⟨b, hb⟩ := mem_iUnion.mp he
  by_contra hn
  exact hb.2 (hspan b ⟨hb.1, hn⟩)

lemma residualUnion_ncard (M : Matroid α) (P A W : B → Set α)
    (hdisj : Pairwise (fun b c => Disjoint (P b) (P c))) :
    (⋃ b, P b \ M.closure (A b ∪ W b)).ncard =
      ∑ b, (P b \ M.closure (A b ∪ W b)).ncard := by
  have hd : Pairwise (fun b c => Disjoint (P b \ M.closure (A b ∪ W b))
      (P c \ M.closure (A c ∪ W c))) := by
    intro b c hbc
    exact (hdisj hbc).mono sdiff_subset sdiff_subset
  simpa only [finsum_eq_sum_of_fintype] using Set.ncard_iUnion_of_finite (fun b => Set.toFinite _) hd

lemma nominal_rank_witnesses (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O : Set α) (ε : Fin 2) :
    ∃ W : ParityWindow (activation h) ε → Set α,
      (∀ b, W b ⊆ nominalLayerSet M hE κ D C h (U : Set α) ε b \ O) ∧
      (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
      (∀ b, nominalLayerSet M hE κ D C h (U : Set α) ε b \ O ⊆
        M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h) ∪ W b)) ∧
      ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
        ∃ β : Z → ParityWindow (activation h) ε,
          ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  choose W hW hc hs using fun b : ParityWindow (activation h) ε => exists_rankWitness M hE
    (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)
    (nominalLayerSet M hE κ D C h (U : Set α) ε b \ O)
  have heq : (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
    unfold nominalRankStatistic
    exact sum_congr rfl (fun b _ => hc b)
  have hd : Pairwise (fun b c => Disjoint (W b) (W c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h (U : Set α) ε hbc).mono
      ((hW b).trans sdiff_subset) ((hW c).trans sdiff_subset)
  obtain ⟨Z, hZU, hZcard, β, hβ⟩ := collect_disjoint_witnesses W U
    (fun b => ((hW b).trans sdiff_subset).trans (nominalLayerSet_subset M hE κ D C h _ ε b)) hd
  refine ⟨W, hW, heq, hs, Z, hZU, ?_, β, hβ⟩
  rwa [heq] at hZcard

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_LabeledFamily
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma groupLabel_mem
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) (i : Fin U.card) :
    groupLabel U i ∈ U :=
  (U.equivFin.symm i).property

lemma exists_groupLabel
    {α : Type u_1} [Fintype α] [LinearOrder α] (U : Finset α) {e : α} (he : e ∈ U) :
    ∃ i, groupLabel U i = e := by
  refine ⟨U.equivFin ⟨e, he⟩, ?_⟩
  simp [groupLabel]

lemma labeledResidualFamily_subsets (M : Matroid α) (U : Finset α) (κ : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ∀ R ∈ labeledResidualFamily M U κ F a ε K, R ⊆ U := by
  rintro R hR e he
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  exact groupLabel_mem U i

lemma labeledResidualFamily_card (M : Matroid α) (hE : M.E = Set.univ)
    (U : Finset α) (hU : U.Nonempty) (κ : ℕ) (hκ : 2 ≤ κ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * U.card) := by
  obtain ⟨d, hd⟩ := hU
  have hc : (labeledResidualFamily M U κ F a ε K).card ≤
      (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card := Finset.card_image_le
  exact (show ((labeledResidualFamily M U κ F a ε K).card : ℝ) ≤
    (integerResidualFamily M U (U.card / κ) F a ε K (groupLabel U)).card by exact_mod_cast hc).trans
      (integerResidualFamily_card_le_exp M hE d U κ hκ F a ε K (groupLabel U) rfl)

lemma nominalResidualSet_eq_labeled (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U Z : Finset α) (ε : Fin 2)
    (W : ParityWindow (activation h) ε → Set α) (β : Z → ParityWindow (activation h) ε)
    (hβ : ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b) :
    (integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β).image (groupLabel U) =
        (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset := by
  classical
  ext e
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨b, hb, hn⟩ := (Finset.mem_filter.mp hi).2
    have hl := (Finset.mem_filter.mp hb).2
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · exact ⟨groupLabel_mem U i, hl⟩
    · simpa only [hβ b] using hn
  · intro he
    obtain ⟨b, hb, hn⟩ := Set.mem_iUnion.mp he
    obtain ⟨i, hi⟩ := exists_groupLabel U hb.1
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hi] using hb.2⟩
    · simpa only [hi, hβ b] using hn

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Deterministic
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayer_le_witness_residual
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (b : ParityWindow (activation h) ε) (W : Set α) :
    (safeLayerSet M hE κ D C T h U I ε b).ncard ≤ κ * W.ncard +
      (nominalLayerSet M hE κ D C h U ε b \
        M.closure (nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h ∪ W)).ncard := by
  by_cases hv : activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0
  · have hx : nominalPath M hE κ D C h (b.val.val - 2) =
        densityExpansion M hE κ (D h) (guardedPath M hE κ D C h (b.val.val - 2)) := by
      unfold nominalPath densityEnabled
      rw [ite_eq_left (by omega)]
    rw [hx]
    apply safe_layer_le_witness_residual M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2)) (lowerCompetition M hE κ D C T b.val.val h)
      W (nominalLayerSet M hE κ D C h U ε b) (safeLayerSet M hE κ D C T h U I ε b)
    intro e he
    exact ⟨⟨hI he.1.1, he.1.2⟩, he.2⟩
  · have he : nominalLayerSet M hE κ D C h U ε b = ∅ := by
      ext e
      constructor
      · exact fun he => (hv ⟨he.2.1, he.2.2.1⟩).elim
      · simp
    simp [safeLayerSet, he]

lemma safeStatistic_le_witness_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (W : ParityWindow (activation h) ε → Set α) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ κ * (∑ b, (W b).ncard) +
      (nominalResidualSet M hE κ D C T h U ε W).ncard := by
  unfold safeLayerStatistic
  calc
    _ ≤ ∑ b, (κ * (W b).ncard +
        (nominalLayerSet M hE κ D C h U ε b \
          M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
            lowerCompetition M hE κ D C T b.val.val h) ∪ W b)).ncard) :=
      sum_le_sum (fun b _ => safeLayer_le_witness_residual M hE κ D C T h U I hI ε b (W b))
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← residualUnion_ncard M _ _ W
        (nominalLayerSet_disjoint M hE κ D C h U ε)]
      rfl

lemma exists_captured_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h)
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2)
    (hzsmall : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ) :
    ∃ R ∈ labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
        (fun b => lowerCompetition M hE κ D C T b.val.val h),
      (R : Set α) ⊆ O ∧ safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
        κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
  classical
  obtain ⟨W, hW, hsum, hspan, Z, hZU, hZcard, β, hβ⟩ :=
    nominal_rank_witnesses M hE κ D C T h U O ε
  let R := (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset
  have hmask : (R : Set α) ⊆ O := by
    intro e he
    exact residualUnion_subset_mask M _ _ W O hspan ((Set.Finite.mem_toFinset _).mp he)
  have hdet : safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
      κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
    have h := safeStatistic_le_witness_residual M hE κ D C T h (U : Set α) I hI ε W
    rwa [hsum, Set.ncard_eq_toFinset_card] at h
  refine ⟨R, ?_, hmask, hdet⟩
  apply Finset.mem_image.mpr
  refine ⟨integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β, ?_, ?_⟩
  · apply nominal_residual_mem_family M hE κ hκ D C h U Z hDU hZU (hZcard.trans hzsmall) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h)
      (fun b => lowerCompetition_subset_guarded M hE κ D C T b.val.val h) β
    · intro w
      have hw : w.val ∈ W (β w) := by
        rw [← hβ (β w)]
        exact ⟨w, rfl, rfl⟩
      exact (hW (β w) hw).1.2.2.2.1
    · exact fun i => hnonloop _ (groupLabel_mem U i)
  · exact nominalResidualSet_eq_labeled M hE κ D C T h U Z ε W β hβ

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Gap
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayerStatistic_le_ncard
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ U.ncard := by
  let L := safeLayerSet M hE κ D C T h U I ε
  have hd : Pairwise (fun b c => Disjoint (L b) (L c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h U ε hbc).mono
      (fun _ he => he.1.2) (fun _ he => he.1.2)
  have heq : (⋃ b, L b).ncard = ∑ b, (L b).ncard := by
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) hd
  rw [show safeLayerStatistic M hE κ D C T h U I ε = ∑ b, (L b).ncard from rfl, ← heq]
  apply Set.ncard_le_ncard _ (Set.toFinite U)
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.2.1

lemma nominalTransferGap_le_bad (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U S : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h) (hS : S ⊆ U)
    (hOS : O ∩ (U : Set α) ⊆ (S : Set α))
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2) :
    nominalTransferGap M hE κ D C T h (U : Set α) O I ε ≤
      residualDelta * U.card + (U.card : ℝ) * residualBadIndicator
        (labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
          (fun b => lowerCompetition M hE κ D C T b.val.val h))
        (residualDelta * U.card) S := by
  classical
  let F := labeledResidualFamily M U κ (guardedPath M hE κ D C h) (activation h) ε
    (fun b => lowerCompetition M hE κ D C T b.val.val h)
  have hn : 0 ≤ residualDelta * (U.card : ℝ) + (U.card : ℝ) *
      residualBadIndicator F (residualDelta * U.card) S := by
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num
  by_cases hz : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ U.card / κ
  · obtain ⟨R, hR, hRO, hdet⟩ := exists_captured_residual M hE κ hκ D C T h U O I
      hDU hI hnonloop ε hz
    have hRU : R ⊆ U := labeledResidualFamily_subsets M U κ _ _ ε _ R hR
    have hRS : R ⊆ S := fun e he => hOS ⟨hRO he, hRU he⟩
    have hcap := capturedResidual_le U S R F hS hR hRS
    have hdet' : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
      exact_mod_cast hdet
    exact max_le (by linarith) hn
  · have hnz : U.card < κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      have hz' := Nat.div_lt_iff_lt_mul hκ |>.mp (lt_of_not_ge hz)
      simpa only [Nat.mul_comm] using hz'
    have hs := safeLayerStatistic_le_ncard M hE κ D C T h (U : Set α) I ε
    rw [Set.ncard_coe_finset] at hs
    have hsz : (safeLayerStatistic M hE κ D C T h (U : Set α) I ε : ℝ) ≤
        (κ : ℝ) * nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
      exact_mod_cast hs.trans hnz.le
    exact max_le (by linarith) hn

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Reverse_Cost
attribute [-instance] _root_.OAI.MatroidProphet.levelMeasurableSpace _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

@[simp] lemma reverseMeanCost_zero (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q cost 0 k S = 0 := by
  simp only [reverseMeanCost, reverseCost, bitsExpectation_const]

end MatroidProphet

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_FocalTransfer
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Finset Pivots
variable {n : ℕ}

lemma trueGroup_nonloop (M : Matroid (Fin n)) (d : MainMasks n)
    (s : Fin n → Option ℤ) (i : ℤ) :
    ∀ e ∈ trueGroup M d s i, e ∉ M.closure ∅ := by
  intro e he hl
  have hc := (mem_trueGroup M d s i e).mp he
  exact hc.1.2.2 (M.closure_mono (Set.empty_subset _) hl)

lemma listedTransferGap_focal_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (Y : Set (Fin n)) (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (ε : Fin 2) (A B C : Finset (Fin n))
    (hA : A ⊆ trueGroup M d s i) (hB : B ⊆ trueGroup M d s i)
    (hC : C ⊆ trueGroup M d s i) :
    listedTransferGap M hE κ (focalMasks d (trueGroup M d s i) A B C) s i Y ε ≤
      residualDelta * (trueGroup M d s i).card + ((trueGroup M d s i).card : ℝ) *
        residualBadIndicator (focalResidualFamily M hE κ d s i ε)
          (residualDelta * (trueGroup M d s i).card) (A ∪ B) := by
  classical
  by_cases hne : A.Nonempty
  · let f := focalMasks d (trueGroup M d s i) A B C
    have hg : groupMask M f s f.D (focalIndex M d s i) = (A : Set (Fin n)) :=
      focal_group_mask M d s i A B C d.D A hA hne hA
    have hDU : groupMask M f s f.D (focalIndex M d s i) ⊆ (trueGroup M d s i : Set (Fin n)) := by
      rw [hg]
      exact hA
    have hI : (f.D : Set (Fin n)) ∩ Y ⊆ groupMask M f s f.D (focalIndex M d s i) := by
      rw [hg, focal_density_inter M d s i A B C Y hY]
      exact Set.inter_subset_left
    have hOS : ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n)) ∩
        (trueGroup M d s i : Set (Fin n)) ⊆ ((A ∪ B : Finset (Fin n)) : Set (Fin n)) := by
      have he := congrArg (fun X : Finset (Fin n) => (X : Set (Fin n)))
        (focal_observed_inter M d s i A B C hA hB)
      simpa only [coe_inter] using he.subset
    have h := nominalTransferGap_le_bad M hE κ hκ (groupMask M f s f.D)
      (groupMask M f s f.C) (groupMask M f s f.T) (focalIndex M d s i)
      (trueGroup M d s i) (A ∪ B) ((f.H ∪ f.D ∪ f.C : Finset (Fin n)) : Set (Fin n))
      ((f.D : Set (Fin n)) ∩ Y) hDU hI (union_subset hA hB) hOS
      (trueGroup_nonloop M d s i) ε
    have hF := funext (focal_incoming_path M hE κ d s i A B C hA hB hC hne)
    have hK := funext (fun b : ParityWindow (activation (focalIndex M d s i)) ε =>
      focal_lowerCompetition M hE κ d s i A B C hA hB hC hne b.val.val)
    rw [hF, hK] at h
    simpa only [listedTransferGap, listedSafeStatistic_focal_nonempty M hE κ d s i A B C Y ε hA hne,
      listedRankStatistic_focal_nonempty M hE κ d s i A B C ε hA hne,
      nominalTransferGap, focalResidualFamily] using h
  · have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst A
    rw [listedTransferGap, listedSafeStatistic_focal_empty, listedRankStatistic_focal_empty]
    simp only [Nat.cast_zero, mul_zero, sub_zero, max_self]
    apply add_nonneg (mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _))
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold residualBadIndicator
    split_ifs <;> norm_num

lemma focalTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      (trueGroup M d s i) (fun A B C =>
        listedTransferGap M hE (2^100) (focalMasks d (trueGroup M d s i) A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  have hu : (1:ℝ)/4 + (1-(1:ℝ)/4)*thinningRate ≤ 1/2 := by norm_num [thinningRate]
  have hne : (trueGroup M d s i).Nonempty := by
    apply card_pos.mp
    have hp := lt_of_lt_of_le constants_positive.2.1 hn
    exact_mod_cast hp
  apply tripleMask_residual_error_le (fun _ => (1:ℝ)/4) (fun _ => thinningRate)
    (fun _ => thinningRate) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1) (fun _ => hu)
    (trueGroup M d s i) (focalResidualFamily M hE (2^100) d s i ε)
  · exact labeledResidualFamily_subsets M _ _ _ _ ε _
  · have hc := labeledResidualFamily_card M hE (trueGroup M d s i) hne (2^100)
        (by norm_num) (guardedPath M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C) (focalIndex M d s i))
        (activation (focalIndex M d s i)) ε
        (fun b => lowerCompetition M hE (2^100)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).D)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).C)
          (groupMask M (focalReference M d s i) s (focalReference M d s i).T) b.val.val (focalIndex M d s i))
    simpa only [Nat.cast_pow, Nat.cast_ofNat, densityThreshold, focalResidualFamily] using hc
  · exact hn
  · intro A hA B hB C hC
    exact listedTransferGap_focal_le M hE (2^100) (by positivity) d s i Y hY ε A B C hA hB hC

end MatroidProphet.MainAlgorithm

end OAI
end

section
-- module Solutions.OAIW2_MatroidSec.MatroidProphet_Residual_Global
attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma tripleMaskExpectation_split (p q r : α → ℝ) (V U : Finset α) (hU : U ⊆ V)
    (f : Finset α → Finset α → Finset α → ℝ) :
    tripleMaskExpectation p q r V f =
      tripleMaskExpectation p q r (V \ U) (fun D C T =>
        tripleMaskExpectation p q r U (fun A B X => f (D ∪ A) (C ∪ B) (T ∪ X))) := by
  unfold tripleMaskExpectation
  rw [bitsExpectation_split p V U hU]
  apply bitsExpectation_congr
  intro D hD
  simp_rw [bitsExpectation_split q V U hU]
  rw [bitsExpectation_comm p q U (V \ U)]
  apply bitsExpectation_congr
  intro C hC
  simp_rw [bitsExpectation_split r V U hU]
  simp_rw [bitsExpectation_comm q r U (V \ U)]
  rw [bitsExpectation_comm p r U (V \ U)]

lemma tripleMaskExpectation_const (p q r : α → ℝ) (V : Finset α) (c : ℝ) :
    tripleMaskExpectation p q r V (fun _ _ _ => c) = c := by
  simp only [tripleMaskExpectation, bitsExpectation_const]

lemma tripleMaskExpectation_congr (p q r : α → ℝ) (V : Finset α)
    {f g : Finset α → Finset α → Finset α → ℝ}
    (h : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V, f D C T = g D C T) :
    tripleMaskExpectation p q r V f = tripleMaskExpectation p q r V g := by
  apply bitsExpectation_congr
  intro D hD
  apply bitsExpectation_congr
  intro C hC
  exact bitsExpectation_congr r V (fun T hT => h D hD C hC T hT)

namespace MainAlgorithm
variable {n : ℕ}

lemma focalMasks_withMasks (d : MainMasks n) (U D C T A B X : Finset (Fin n))
    (hD : D ⊆ univ \ U) (hC : C ⊆ univ \ U) (hT : T ⊆ univ \ U) :
    focalMasks (withMasks d D C T) U A B X = withMasks d (D ∪ A) (C ∪ B) (T ∪ X) := by
  have hD' : D \ U = D := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hD he)).2⟩⟩
  have hC' : C \ U = C := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hC he)).2⟩⟩
  have hT' : T \ U = T := by ext e; simp only [mem_sdiff]; exact ⟨And.left, fun he => ⟨he, (mem_sdiff.mp (hT he)).2⟩⟩
  simp only [focalMasks, withMasks, hD', hC', hT']

lemma listedTransferGap_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) (ε : Fin 2) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => listedTransferGap M hE (2^100) (withMasks d A B C) s i Y ε) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  rw [tripleMaskExpectation_split _ _ _ univ (trueGroup M d s i) (subset_univ _)]
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  calc
    _ ≤ tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
        (univ \ trueGroup M d s i) (fun _ _ _ => 2 * residualDelta * (trueGroup M d s i).card) := by
      apply tripleMaskExpectation_mono _ _ _ (fun _ => by norm_num) (fun _ => by norm_num)
        (fun _ => ht0) (fun _ => ht1) (fun _ => ht0) (fun _ => ht1)
      intro D hD C hC T hT
      have hh := focalTransferGap_expectation_le M hE (withMasks d D C T) s i Y hY hn ε
      apply le_trans ?_ hh
      apply le_of_eq
      apply tripleMaskExpectation_congr
      intro A hA B hB X hX
      rw [trueGroup_withMasks, focalMasks_withMasks d _ D C T A B X hD hC hT]
    _ = _ := tripleMaskExpectation_const _ _ _ _ _

lemma listedTransferGap_parity_expectation_le_oai (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => fairParityExpectation (fun p =>
        listedTransferGap M hE (2^100) (withMasks d A B C) s i Y (boolParity p))) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  have h0 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity false)
  have h1 := listedTransferGap_expectation_le M hE d s i Y hY hn (boolParity true)
  simp only [fairParityExpectation, div_eq_mul_inv, mul_comm _ ((2:ℝ)⁻¹)]
  rw [tripleMaskExpectation_mul, tripleMaskExpectation_add]
  linarith

end MainAlgorithm
end MatroidProphet

end OAI
end

theorem solution : type_of% @OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le_oai := @OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le_oai
