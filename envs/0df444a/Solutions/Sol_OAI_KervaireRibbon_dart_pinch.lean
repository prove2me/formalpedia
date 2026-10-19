-- Prove2me | solution 1 for OAI.KervaireRibbon.dart_pinch
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:13:07.698832+00:00
-- url     : https://prove2.me/submissions/85c195a4-17b6-485e-9dd9-b62054a00bb7

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles

open OAI OAI.KervaireRibbon
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
universe u v

section kr_words
open Monoid.CoprodI

theorem kr_w_split {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, DecidableEq (M i)] (w : Word M) {i : ι} {m : M i} {rest : List (Σ i, M i)}
    (h : w.toList = ⟨i, m⟩ :: rest) :
    ∃ w' : Word M, w'.toList = rest ∧ w'.fstIdx ≠ some i ∧ m ≠ 1 ∧ w = of m • w' := by
  have hc := w.chain_ne
  rw [h] at hc
  let w' : Word M := ⟨rest, fun l hl => w.ne_one l (by rw [h]; exact List.mem_cons_of_mem _ hl),
    (List.isChain_cons.mp hc).2⟩
  have hf : w'.fstIdx ≠ some i := Word.fstIdx_ne_iff.mpr (List.isChain_cons.mp hc).1
  have hm : m ≠ 1 := w.ne_one ⟨i, m⟩ (by rw [h]; exact List.mem_cons_self)
  refine ⟨w', rfl, hf, hm, ?_⟩
  rw [← Word.cons_eq_smul (h1 := hf) (h2 := hm)]
  apply Word.ext
  simp [h, w']

theorem kr_w_cons {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, DecidableEq (M i)] (w : Word M) {i : ι} (m : M i) (hf : w.fstIdx ≠ some i) (hm : m ≠ 1) :
    (of m • w).toList = ⟨i, m⟩ :: w.toList := by
  rw [← Word.cons_eq_smul (h1 := hf) (h2 := hm)]
  rfl

theorem kr_w_merge {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, DecidableEq (M i)] (w : Word M) {i : ι} {m n : M i} {rest : List (Σ i, M i)}
    (h : w.toList = ⟨i, m⟩ :: rest) (hnm : n * m ≠ 1) :
    (of n • w).toList = ⟨i, n * m⟩ :: rest := by
  obtain ⟨w', h1, hf, hm, rfl⟩ := kr_w_split w h
  rw [smul_smul, ← map_mul, kr_w_cons w' _ hf hnm, h1]

end kr_words

abbrev KrM (A : Type u) : Bool → Type u := fun b => cond b A (ULift.{u} (Multiplicative ℤ))

instance kr_instGroup (A : Type u) [Group A] : ∀ b, Group (KrM A b) := fun b =>
  match b with
  | true => (inferInstance : Group A)
  | false => (inferInstance : Group (ULift.{u} (Multiplicative ℤ)))

noncomputable def krPhi (A : Type u) [Group A] : FreeProd A →* Monoid.CoprodI (KrM A) :=
  Monoid.Coprod.lift (Monoid.CoprodI.of (M := KrM A) (i := true))
    ((Monoid.CoprodI.of (M := KrM A) (i := false)).comp (MulEquiv.ulift.symm.toMonoidHom))

theorem kr_dart_nf {D : Type v} {A : Type u} [Group A] (t : D → ℤ) (c : D → A) :
    ∀ (l : List D) (d : D), (∀ e ∈ d::l, t e = 1 ∨ t e = -1) →
    (∀ pre post x y, d::l = pre ++ x :: y :: post → c x = 1 → t y ≠ -t x) →
    ∃ (m : ULift.{u} (Multiplicative ℤ)) (rest : List (Σ i, KrM A i)),
      (krPhi A (dartEval t c (d::l)) • (Monoid.CoprodI.Word.empty)).toList =
        (⟨false, m⟩ : Σ i, KrM A i) :: rest ∧ 0 < t d * Multiplicative.toAdd m.down := by
  have hletter : ∀ (d : D) (w : Monoid.CoprodI.Word (KrM A)),
      krPhi A (dartLetter t c d) • w = Monoid.CoprodI.of (M := KrM A) (i := false)
        (ULift.up (Multiplicative.ofAdd (t d))) • (Monoid.CoprodI.of (M := KrM A) (i := true) (c d) • w) := by
    intro d w
    simp only [dartLetter, map_mul, mul_smul, krPhi, Monoid.Coprod.lift_apply_inl,
      Monoid.Coprod.lift_apply_inr, MonoidHom.comp_apply]
    rfl
  have hstep : ∀ (d : D) (w : Monoid.CoprodI.Word (KrM A)), (t d = 1 ∨ t d = -1) →
      w.fstIdx ≠ some true → (c d = 1 → w.fstIdx ≠ some false) →
      ∃ (m : ULift.{u} (Multiplicative ℤ)) (rest : List (Σ i, KrM A i)),
        (krPhi A (dartLetter t c d) • w).toList = (⟨false, m⟩ : Σ i, KrM A i) :: rest ∧
          0 < t d * Multiplicative.toAdd m.down := by
    intro d w ht hf' hf
    rw [hletter]
    have hn : (ULift.up (Multiplicative.ofAdd (t d)) : KrM A false) ≠ 1 := by
      intro h
      have := congrArg (fun z : ULift.{u} (Multiplicative ℤ) => Multiplicative.toAdd z.down) h
      simp at this
      rcases ht with h' | h' <;> rw [h'] at this <;> simp at this
    by_cases hc : c d = 1
    · have : Monoid.CoprodI.of (M := KrM A) (i := true) (c d) • w = w := by
        rw [hc]; simp
      rw [this]
      refine ⟨ULift.up (Multiplicative.ofAdd (t d)), w.toList, kr_w_cons w _ (hf hc) hn, ?_⟩
      rcases ht with h' | h' <;> simp [h']
    · have h1 := kr_w_cons (i := true) w (c d) hf' hc
      have hf2 : (Monoid.CoprodI.of (M := KrM A) (i := true) (c d) • w).fstIdx ≠ some false := by
        rw [Monoid.CoprodI.Word.fstIdx, h1]; simp
      refine ⟨ULift.up (Multiplicative.ofAdd (t d)), _, kr_w_cons _ _ hf2 hn, ?_⟩
      rcases ht with h' | h' <;> simp [h']
  intro l
  induction l with
  | nil =>
    intro d ht _
    have : dartEval t c [d] = dartLetter t c d := by simp [dartEval]
    rw [this]
    exact hstep d _ (ht d (by simp)) (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty])
      (fun _ => by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty])
  | cons e l ih =>
    intro d ht hnp
    obtain ⟨m, rest, hw, hpos⟩ := ih e (fun x hx => ht x (List.mem_cons_of_mem _ hx))
      (fun pre post x y h => hnp (d :: pre) post x y (by rw [h]; rfl))
    rw [dartEval_cons, map_mul, mul_smul]
    set w := krPhi A (dartEval t c (e :: l)) • (Monoid.CoprodI.Word.empty (M := KrM A)) with hwdef
    have htd := ht d (by simp)
    have hte := ht e (by simp)
    by_cases hc : c d = 1
    · have hsame : t e = t d := by
        have := hnp [] l d e rfl hc
        rcases htd with h1 | h1 <;> rcases hte with h2 | h2 <;> omega
      rw [hletter, hc, map_one, one_smul]
      have hne : (ULift.up (Multiplicative.ofAdd (t d)) : KrM A false) * m ≠ 1 := by
        intro h
        have := congrArg (fun z : ULift.{u} (Multiplicative ℤ) => Multiplicative.toAdd z.down) h
        change t d + Multiplicative.toAdd m.down = 0 at this
        rw [hsame] at hpos
        rcases htd with h1 | h1 <;> rw [h1] at this hpos <;> omega
      refine ⟨_, rest, kr_w_merge w hw hne, ?_⟩
      change 0 < t d * (t d + Multiplicative.toAdd m.down)
      rw [hsame] at hpos
      rcases htd with h1 | h1 <;> rw [h1] at hpos ⊢ <;> omega
    · exact hstep d w htd (by rw [Monoid.CoprodI.Word.fstIdx, hw]; simp) (fun h => absurd h hc)

theorem solution (t : D → ℤ) (c : D → A) (l : List D) (hl : l ≠ [])
    (ht : ∀ d ∈ l, t d = 1 ∨ t d = -1) (g : A)
    (he : dartEval t c l = Coprod.inl g) :
    ∃ pre post x y, l = pre ++ x::y::post ∧ c x = 1 ∧ t y = -t x := by
  by_contra hcon
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨m, rest, hw, -⟩ := kr_dart_nf t c l' d ht (fun pre post x y h hx hy => hcon ⟨pre, post, x, y, h, hx, hy⟩)
  rw [he] at hw
  have : krPhi A (Coprod.inl g) = Monoid.CoprodI.of (M := KrM A) (i := true) g := by
    simp [krPhi]
  rw [this] at hw
  by_cases hg : g = 1
  · subst hg; simp at hw
  · rw [kr_w_cons _ _ (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty]) hg] at hw
    simp at hw

