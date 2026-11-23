-- Prove2me | solution 1 for LinearSetReconciliation327.Main.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-23T11:19:56.662618+00:00
-- url     : https://prove2.me/submissions/7f0b84e1-760e-4bde-9dc8-8ebed9997d95

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_17
import Definitions.Def_LinearSetReconciliation327_Main_HintCleanParams20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintProgramFree20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream2320261120

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

open Finset
open scoped ENNReal

private theorem hintWidthOK_grow {W U factor : ℕ} {c L : ℝ}
    (hFactor : 1 ≤ factor) (h : WidthOK W U c L) :
    WidthOK (factor * W) U ((factor : ℝ) * c) L := by
  have hW : W ≤ factor * W := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hFactor
  refine ⟨h.1.trans hW, h.2.1.trans hW, ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h.2.2 (Nat.cast_nonneg _)

private theorem hintCleanProbability (KCR : ℝ) (n lam N X Y fuel : ℕ) (T : Node)
    (hArgs : (HintCleanParams.hintP KCR n lam).NodeArgs N X Y)
    (hTree : (HintCleanParams.hintP KCR n lam).tree fuel N X Y = some T) :
    T.BoundsProb ((2 : ℝ) ^ (HintCleanParams.hintP KCR n lam).lamStar)⁻¹ X Y := by
  let P := HintCleanParams.hintP KCR n lam
  let A := HintCleanParams.hintLenA KCR
  let C := HintCleanParams.hintLenC KCR
  have h54 : HintCleanParams.hintLenC₀₅₄ KCR ≤ C := by
    unfold C HintCleanParams.hintLenC
    omega
  have h56 : HintCleanParams.hintLenC₀₅₆ KCR ≤ C := by
    unfold C HintCleanParams.hintLenC
    omega
  have hZ := Classical.choose_spec (Classical.choose_spec HintUpstream54.lemma_5_4 A
    (HintCleanParams.le_hintLenA₅₄ KCR)) C h54 n lam
  have hUV := Classical.choose_spec (Classical.choose_spec HintUpstream56.lemma_5_6 A
    (HintCleanParams.le_hintLenA₅₆ KCR)) C h56 n lam
  exact HintBoundsBudget.c8_boundsProb_tree (P := P)
    (fun m x y h hn s j hv => (hZ m x y h hn s j hv).2)
    (fun m x y h hr s j hv col => (hUV m x y h hr s j hv col).2.2)
    fuel N X Y T hTree hArgs

private theorem hintCleanColumn (S : CRSourceBundle) (n lam N X Y fuel : ℕ) (T : Node)
    (hT : IsSchemeTree (HintCleanParams.hintP S.K n lam) T)
    (hArgs : (HintCleanParams.hintP S.K n lam).NodeArgs N X Y)
    (hTree : (HintCleanParams.hintP S.K n lam).tree fuel N X Y = some T)
    (hCount : (T.nodeCount : ℝ) ≤ HintCleanParams.hintLenK₁₀ * (HintCleanParams.hintLenA S.K : ℝ) * lg n ^ 27)
    (r : (hintSpec T).Seed) :
    ColumnWeightLE (hintH_trees (crFamily S) (HintCleanParams.hintP S.K n lam) T hT r)
      (HintProgramFree.hintCu (HintProgramFree.hintColK S.K) * lg n ^ HintProgramFree.hintpu) := by
  let P := HintCleanParams.hintP S.K n lam
  let CR := crFamily S
  let Bℓ := HintProgramFree.colBℓ S.K n
  let Bc := HintProgramFree.colBc S.K n
  have hShrink := HintProgramFree.tree_shrink (KCR := S.K) (P := P) rfl rfl hArgs.1 fuel N X Y T
    hTree hArgs.2.2.1 hArgs.2.2.2.1 hArgs.2.2.2.2.1 hArgs.2.2.2.2.2
  have hCols : HintProgramFree.ColNodeOK CR Bℓ Bc T :=
    HintProgramFree.colNodeOK_of_shrink (n := n) (crFamily_columns S) T hShrink
  have hB : 1 ≤ Bℓ := HintProgramFree.colBℓ_pos hArgs.1
  intro i
  have hCard :
      (univ.filter fun p : Fin (synLen CR T) => hintH_trees CR P T hT r (Pi.single i 1) p = 1).card ≤
        T.nodeCount * (Bℓ + Bc) := by
    have hSketch :
        (univ.filter fun p : Fin (synLen CR T) => hintH_trees CR P T hT r (Pi.single i 1) p = 1).card =
          HintProgramFree.colWeight CR T (hintKappa P T hT r) {i.val} := by
      rw [HintProgramFree.colWeight_eq_card]
      simp only [HintProgramFree.colSupp, hintH_trees_apply, support_single]
    rw [hSketch]
    exact HintProgramFree.colWeight_singleton_le CR Bℓ Bc hB T hCols (hintKappa P T hT r) i.val i.isLt
  calc
    _ ≤ ((T.nodeCount * (Bℓ + Bc) : ℕ) : ℝ) := by exact_mod_cast hCard
    _ = (T.nodeCount : ℝ) * ((Bℓ : ℝ) + Bc) := by push_cast; ring
    _ ≤ _ := HintProgramFree.nodeCol_bound hArgs.1 hCount

theorem hintSketch_from_cr (S : CRSourceBundle) :
    ∃ (progUp progDec : Program) (cW α C₁ C₂ C₃ Cu Cd : ℝ) (p₁ pu : ℕ),
      0 < cW ∧ 0 ≤ α ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < Cu ∧ 0 < Cd ∧
      ∀ n lam N X Y : ℕ, 2 ≤ n → 1 ≤ lam → 1 ≤ N → N ≤ n → X ≤ N → Y ≤ N →
        ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
          (H : spec.Seed → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
          WidthOK W n cW (lg n) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
          (M : ℝ) ≤ (1 + C₁ / lg n) * ((X : ℝ) + α * hN N Y) + C₂ * ((N : ℝ) / lg n ^ 8) +
            C₃ * (lam : ℝ) * lg n ^ p₁ ∧
          (∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)) ∧
          (∀ r, TogglesWithin progUp (spec.env W det r) (H r) (Cu * lg n ^ pu)) ∧
          -- worst-case time: every seed, every stored vector, every hint list
          (∀ (r : spec.Seed) (y : Fin M → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) →
            ∃ s' : RAMState, HaltsWithin progDec (spec.env W det r)
              (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W y J) s') ∧
          -- the matrices do not depend on the hint; recovery of each fixed input and hint with (3)
          (∀ (x : Fin N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) → J.length ≤ X →
            ((univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).card ≤ Y) →
            prU (fun r : spec.Seed => ¬ ∃ s' : RAMState,
                HaltsWithin progDec (spec.env W det r)
                  (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W (H r x) J) s' ∧
                OutputsSupport s' x) ≤ ((2 : ℝ) ^ lam)⁻¹) := by
  classical
  let A := HintCleanParams.hintLenA S.K
  let C := HintCleanParams.hintLenC S.K
  let K := HintCleanParams.hintLenK₁₀
  let Kcol := HintCleanParams.hintColK S.K
  let Klen := HintProgramFree.hintLenK S.K
  let B := HintCleanParams.hintLenK₁₀bits S.K
  let growth := hintWidthScale (hintResourceCoefficient S A C K) (hintResourceDegree S)
  let cW₀ := HintProgramFree.hintcW Kcol
  let cW := (8 * (growth : ℝ)) * cW₀
  let α := HintProgramFree.hintLenAlpha S.K Klen
  let C₁ := HintProgramFree.hintLenC₁ S.K Klen
  let C₂ := HintProgramFree.hintLenC₂ S.K Klen
  let C₃ := HintProgramFree.hintLenC₃' S.K Klen
  let p₁ := HintProgramFree.hintLenP₁ S.K
  let pu := HintCleanParams.hintpu
  let Cu₀ := HintCleanParams.hintCu Kcol
  let Cu := 3 * Cu₀
  let Cd := hintDecoderTimeConstant S A C K
  have hK : 0 < K := HintCleanParams.hintLenK₁₀_pos
  have hColK : 0 < Kcol := HintProgramFree.hintColK_pos S.K
  have hLenK : 0 < Klen := HintProgramFree.hintLenK_pos S.K
  have hGrowth : 1 ≤ growth := hintWidthScale_pos _ _
  have hGrowth' : 0 < (growth : ℝ) := by exact_mod_cast hGrowth
  have hWordC : 0 < cW := by unfold cW cW₀ HintProgramFree.hintcW; positivity
  have hCu₀ : 0 < Cu₀ := by unfold Cu₀ HintCleanParams.hintCu; positivity
  have hCu : 0 < Cu := by unfold Cu; positivity
  have hAlpha : 0 ≤ α := (HintProgramFree.hintLenAlpha_pos S.K hLenK).le
  have hC₁ := HintProgramFree.hintLenC₁_nonneg (KCR := S.K) hLenK
  have hC₂ := HintProgramFree.hintLenC₂_nonneg (KCR := S.K) hLenK
  have hC₃ : 0 ≤ C₃ := by
    have hC₃₀ := HintProgramFree.hintLenC₃_nonneg S.K hLenK
    unfold C₃ HintProgramFree.hintLenC₃'
    positivity
  have hB : K ≤ (2 : ℝ) ^ B := by
    apply (Nat.le_ceil K).trans
    exact_mod_cast (show ⌈K⌉₊ ≤ 2 ^ B from
      (Nat.le_add_right _ 2).trans ((Nat.le_pow_clog (by norm_num : 1 < 2) (⌈K⌉₊ + 2)).trans
        (Nat.pow_le_pow_right (by decide) (by unfold B HintCleanParams.hintLenK₁₀bits K; omega))))
  have hCap : B + 3 * A ≤ C := by unfold B A C HintCleanParams.hintLenC; omega
  have h27 : 27 ≤ C := by unfold C HintCleanParams.hintLenC; omega
  refine ⟨progUpSaved, hintNativeProgram S, cW, α, C₁, C₂, C₃, Cu, Cd, p₁, pu,
    hWordC, hAlpha, hC₁, hC₂, hC₃, hCu, hintDecoderTimeConstant_pos S A C K, ?_⟩
  intro n lam N X Y hn hLam hN hNn hX hY
  let H := HintCleanParams.hintP S.K n lam
  have hArgs : H.NodeArgs N X Y := ⟨hn, hLam, hN, hNn, hX, hY⟩
  obtain ⟨fuel, T, hTree, _, _, _, hCount⟩ := HintCleanParams.lemma_5_10_at S.K n lam N X Y hArgs
  let base := HintCleanParams.hintW Kcol n
  let Bc := colBc S.K n
  let W := upWideWord (growth * base)
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  let previous : ℕ → ℕ := fun _ => 0
  have hPrep := HintCleanParams.upHint_prepared (crFamily_rows S) (crFamily_columns S)
    (fun m t _ i _ => crFamily_range S m t i) hArgs fuel T hTree
  have hBaseLog : Nat.clog 2 (n + 2) ≤ base := HintCleanParams.up_hintW_clog Kcol n
  have hBase : 1 ≤ base := (by decide : 1 ≤ 8).trans hPrep.word_min
  have hProb := hintCleanProbability S.K n lam N X Y fuel T hArgs hTree
  obtain ⟨hT, hRoot, hFits, hTotal, hCorrect⟩ :=
    hintActualDecoder_of_bounds S H K B N X Y fuel base T hArgs hTree hK.le hB hCap h27 hCount
      hBase hBaseLog hProb previous
  obtain ⟨_, _, _, hLengthAll⟩ := HintProgramFree.hintLengthOK (KCR := S.K)
  have hLength := hLengthAll n lam N X Y (crFamily S) (crFamily_rows S) hArgs fuel T hTree
  have hBaseWidth : WidthOK base n cW₀ (lg n) := HintProgramFree.hintWidthOK hColK.le hn
  have hWidth : WidthOK W n cW (lg n) := by
    have hg : 1 ≤ 8 * growth := by omega
    have hw := hintWidthOK_grow hg hBaseWidth
    simpa only [W, upWideWord, cW, Nat.mul_assoc, Nat.cast_mul, Nat.cast_ofNat] using hw
  have hBaseLe : base ≤ W := by
    have hG : base ≤ growth * base := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right base hGrowth
    exact hG.trans (upWideWord_ge _)
  have hWords : wordsOf W (synLen (crFamily S) T) ≤ 2 ^ W :=
    (wordsOf_antitone_word hBase hBaseLe).trans
      (hPrep.words.trans (Nat.pow_le_pow_right (by decide) hBaseLe))
  subst N
  let D := hintDecoderTables S H hT W Bc header
  let det := D.det S H (upRootDet (crFamily S) (growth * base) Bc T) previous header T.N
  refine ⟨W, synLen (crFamily S) T, hintSpec T, det, hintH_trees (crFamily S) H T hT,
    hWidth, hFits, hWords, ?_, ?_, ?_, hTotal, hCorrect⟩
  · unfold HintProgramFree.HintLengthOK at hLength
    with_unfolding_all exact hLength
  · intro r
    have hCol := hintCleanColumn S n lam T.N X Y fuel T hT hArgs hTree hCount r
    intro i
    apply (hCol i).trans
    have hLg : 0 ≤ lg (n : ℝ) ^ pu := pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_lg hn)) _
    change Cu₀ * lg (n : ℝ) ^ pu ≤ (3 * Cu₀) * lg (n : ℝ) ^ pu
    exact mul_le_mul_of_nonneg_right (by linarith) hLg
  · intro r
    have hTime : ((125 * (T.nodeCount * (T.depth + HintCleanParams.colBℓ S.K n + Bc)) + 12 : ℕ) : ℝ) ≤
        Cu₀ * lg (n : ℝ) ^ pu := hPrep.cost
    have hToggle := hintSavedToggles_grown S H hT base growth Bc n (HintCleanParams.colBℓ S.K n)
      (Cu₀ * lg (n : ℝ) ^ pu) previous hGrowth hPrep.word_min hPrep.fits hPrep.words hPrep.static
      hPrep.universe_fits hPrep.positive hPrep.padding hPrep.ell_pos hPrep.ell hTime r
    convert hToggle using 1
    unfold Cu
    ring

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSketch_from_cr

set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open Finset

theorem hintCRSource_clean : Nonempty CRSourceBundle := by
  classical
  obtain ⟨progUp, progDec, K, cW, hK, hcW, hAll⟩ := HintUpstream23.proposition_2_3
  have hPackets : ∀ N t, ∃ d : CRSourcePacket N t,
      ((1 ≤ N ∧ t ≤ N) → CRSourcePacketSpec progUp progDec K cW N t d) ∧
        (¬ (1 ≤ N ∧ t ≤ N) → d = crSourceEmpty N t) := by
    intro N t
    by_cases hValid : 1 ≤ N ∧ t ≤ N
    · obtain ⟨W, R, det, H, hSpec⟩ := hAll N t hValid.1 hValid.2
      refine ⟨⟨W, R, det, H⟩, ?_, ?_⟩
      · intro h
        exact hSpec
      · intro h
        exact (h hValid).elim
    · refine ⟨crSourceEmpty N t, ?_, ?_⟩
      · intro h
        exact (hValid h).elim
      · intro h
        rfl
  choose data hSpec hInvalid using hPackets
  exact ⟨⟨progUp, progDec, K, cW, hK, hcW, data,
    fun N t hN ht => hSpec N t ⟨hN, ht⟩, hInvalid⟩⟩

theorem hintSketch_formalized :
    ∃ (progUp progDec : Program) (cW α C₁ C₂ C₃ Cu Cd : ℝ) (p₁ pu : ℕ),
      0 < cW ∧ 0 ≤ α ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < Cu ∧ 0 < Cd ∧
      ∀ n lam N X Y : ℕ, 2 ≤ n → 1 ≤ lam → 1 ≤ N → N ≤ n → X ≤ N → Y ≤ N →
        ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
          (H : spec.Seed → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
          WidthOK W n cW (lg n) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
          (M : ℝ) ≤ (1 + C₁ / lg n) * ((X : ℝ) + α * hN N Y) + C₂ * ((N : ℝ) / lg n ^ 8) +
            C₃ * (lam : ℝ) * lg n ^ p₁ ∧
          (∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)) ∧
          (∀ r, TogglesWithin progUp (spec.env W det r) (H r) (Cu * lg n ^ pu)) ∧
          -- worst-case time: every seed, every stored vector, every hint list
          (∀ (r : spec.Seed) (y : Fin M → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) →
            ∃ s' : RAMState, HaltsWithin progDec (spec.env W det r)
              (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W y J) s') ∧
          -- the matrices do not depend on the hint; recovery of each fixed input and hint with (3)
          (∀ (x : Fin N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) → J.length ≤ X →
            ((univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).card ≤ Y) →
            prU (fun r : spec.Seed => ¬ ∃ s' : RAMState,
                HaltsWithin progDec (spec.env W det r)
                  (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W (H r x) J) s' ∧
                OutputsSupport s' x) ≤ ((2 : ℝ) ^ lam)⁻¹) := by
  obtain ⟨S⟩ := hintCRSource_clean
  exact hintSketch_from_cr S

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main Finset in
theorem solution :
    ∃ (progUp progDec : Program) (cW α C₁ C₂ C₃ Cu Cd : ℝ) (p₁ pu : ℕ),
      0 < cW ∧ 0 ≤ α ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < Cu ∧ 0 < Cd ∧
      ∀ n lam N X Y : ℕ, 2 ≤ n → 1 ≤ lam → 1 ≤ N → N ≤ n → X ≤ N → Y ≤ N →
        ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
          (H : spec.Seed → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
          WidthOK W n cW (lg n) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
          (M : ℝ) ≤ (1 + C₁ / lg n) * ((X : ℝ) + α * hN N Y) + C₂ * ((N : ℝ) / lg n ^ 8) +
            C₃ * (lam : ℝ) * lg n ^ p₁ ∧
          (∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)) ∧
          (∀ r, TogglesWithin progUp (spec.env W det r) (H r) (Cu * lg n ^ pu)) ∧
          -- worst-case time: every seed, every stored vector, every hint list
          (∀ (r : spec.Seed) (y : Fin M → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) →
            ∃ s' : RAMState, HaltsWithin progDec (spec.env W det r)
              (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W y J) s') ∧
          -- the matrices do not depend on the hint; recovery of each fixed input and hint with (3)
          (∀ (x : Fin N → ZMod 2) (J : List ℕ), J.Nodup → (∀ v ∈ J, v < N) → J.length ≤ X →
            ((univ.filter fun i : Fin N => x i = 1 ∧ i.val ∉ J).card ≤ Y) →
            prU (fun r : spec.Seed => ¬ ∃ s' : RAMState,
                HaltsWithin progDec (spec.env W det r)
                  (Cd * (N : ℝ) * Real.exp (Cd * lg (lg n) ^ 2)) (decoderStart W (H r x) J) s' ∧
                OutputsSupport s' x) ≤ ((2 : ℝ) ^ lam)⁻¹) :=
  LinearSetReconciliation327.Main.hintSketch_formalized

-- #print axioms solution
