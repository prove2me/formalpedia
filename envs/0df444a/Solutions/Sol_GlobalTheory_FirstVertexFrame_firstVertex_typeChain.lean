-- Prove2me | solution 1 for GlobalTheory.FirstVertexFrame.firstVertex_typeChain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:15.607006+00:00
-- url     : https://prove2.me/submissions/3b0ca9be-1edb-432b-9da7-026400abb240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_inv
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_val
import Theorems.Thm_GlobalTheory_StepData_Model_wt_ne_zero
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_zero
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
import Theorems.Thm_GlobalTheory_StepData_mem_prX
import Theorems.Thm_GlobalTheory_StepData_reGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
namespace GlobalTheory.FirstVertexFrame
section
variable {k : Type} [Field k] {t : Type} [Fintype t] [DecidableEq t] {κ l : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
open MeasureTheory ValuativeRel Matrix Topology in
private lemma stdOrd_ixZero_inr (t : Type) {κ l : ℕ} (H : 0 + l = l) (i : Fin l) :
    _root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t (Sum.inr i)) = Sum.inr i := by
  have hf : ∀ x : Fin (l + 0), (finSumFinEquiv.symm x : Fin l ⊕ Fin 0) = Sum.inl x := by
    intro x
    rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
    rfl
  simp [_root_.GlobalTheory.StepData.stdOrd, _root_.GlobalTheory.StepData.ixZero, hf]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma wt_stdOrd_ixZero {k : Type} [Field k] (t : Type) {κ l : ℕ} (ϖ : kˣ) (H : 0 + l = l)
    (r : Fin κ ⊕ Fin l) :
    _root_.GlobalTheory.StepData.Model.wt ϖ (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t r)) =
      _root_.GlobalTheory.StepData.Model.wt ϖ r := by
  rcases r with i | i
  · rfl
  · simp only [stdOrd_ixZero_inr]
    rfl
open MeasureTheory ValuativeRel Matrix Topology in
private lemma typeFrame_ord {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ)
    (o : ι ≃ n ⊕ Fin c) : (_root_.GlobalTheory.StepData.typeFrame ϖ o).ord = o := rfl
open MeasureTheory ValuativeRel Matrix Topology in
private lemma read_apply_eq_stdOrd_mul_wt {k : Type} [Field k] (t : Type) [Fintype t] [DecidableEq t] {κ l : ℕ} (ϖ : kˣ)
    (H : 0 + l = l) (x : GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0 ⊕ Fin l) k) (r r' : Fin κ ⊕ Fin l) :
    (_root_.GlobalTheory.FirstVertexFrame.read t ϖ H x : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) r r' =
      (_root_.GlobalTheory.StepData.Model.wt ϖ r)⁻¹ *
        (x : Matrix _ _ k) (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t r))
          (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t r')) *
        _root_.GlobalTheory.StepData.Model.wt ϖ r' := by
  obtain ⟨g, rfl⟩ := (_root_.GlobalTheory.StepData.typeFrame ϖ
    (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H)).conj.surjective x
  rw [← wt_stdOrd_ixZero t ϖ H r, ← wt_stdOrd_ixZero t ϖ H r']
  simp only [_root_.GlobalTheory.FirstVertexFrame.read, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  simp only [_root_.GlobalTheory.StepData.reGL_symm_val, _root_.GlobalTheory.StepData.LatFrame.conj_apply, Units.val_mul,
    _root_.GlobalTheory.StepData.Model.typeFrame_val, _root_.GlobalTheory.StepData.Model.typeFrame_inv,
    _root_.GlobalTheory.StepData.reGL_val, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, typeFrame_ord,
    Equiv.symm_apply_apply]
  have h1 := _root_.GlobalTheory.StepData.Model.wt_ne_zero ϖ
    (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t r))
  have h2 := _root_.GlobalTheory.StepData.Model.wt_ne_zero ϖ
    (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t r'))
  field_simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma coe_embX_eq_fromBlocks {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c : ℕ) (g : GL n k) :
    ((_root_.GlobalTheory.RootEx.embX c g : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) =
      Matrix.fromBlocks (g : Matrix n n k) 0 0 1 := by
  unfold _root_.GlobalTheory.RootEx.embX
  simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma stdOrd_ixZero_inl (t : Type) {κ l : ℕ} (H : 0 + l = l) (i : Fin κ) :
    _root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t (Sum.inl i)) =
      Sum.inl (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t i) := rfl
open MeasureTheory ValuativeRel Matrix Topology in
private lemma read_embX_eq_embX_reGL_symm {k : Type} [Field k] (t : Type) [Fintype t] [DecidableEq t] {κ l : ℕ} (ϖ : kˣ)
    (H : 0 + l = l) (γ : GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) k) :
    _root_.GlobalTheory.FirstVertexFrame.read t ϖ H (_root_.GlobalTheory.RootEx.embX l γ) =
      _root_.GlobalTheory.RootEx.embX l
        ((_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t)).symm γ) := by
  ext r r'
  rw [read_apply_eq_stdOrd_mul_wt, coe_embX_eq_fromBlocks, coe_embX_eq_fromBlocks, _root_.GlobalTheory.StepData.reGL_symm_val]
  have hw1 : ∀ i : Fin κ, _root_.GlobalTheory.StepData.Model.wt (c := l) ϖ (Sum.inl i) = 1 := fun _ => rfl
  have hw : ∀ m : Fin l, _root_.GlobalTheory.StepData.Model.wt (n := Fin κ) ϖ (Sum.inr m) ≠ 0 :=
    fun m => _root_.GlobalTheory.StepData.Model.wt_ne_zero ϖ _
  rcases r with i | i <;> rcases r' with j | j
  · simp [stdOrd_ixZero_inl, hw1]
  · simp [stdOrd_ixZero_inl, stdOrd_ixZero_inr]
  · simp [stdOrd_ixZero_inl, stdOrd_ixZero_inr]
  · simp only [stdOrd_ixZero_inr, fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs with h
    · subst h
      field_simp [hw i]
    · simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma read_mem_N_iff {k : Type} [Field k] (t : Type) [Fintype t] [DecidableEq t] {κ l : ℕ}
    (ϖ : kˣ) (H : 0 + l = l) (u : GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0 ⊕ Fin l) k) :
    _root_.GlobalTheory.FirstVertexFrame.read t ϖ H u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1 ↔
      u ∈ _root_.GlobalTheory.RootEx.N k (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) l 1 := by
  rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff, _root_.GlobalTheory.RootEx.Model.mem_N_iff]
  unfold _root_.GlobalTheory.RootEx.InN
  let σ : (Fin κ ⊕ Fin l) ≃ (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0 ⊕ Fin l) :=
    (_root_.GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin l) t).trans (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H)
  have hpos : ∀ r, _root_.GlobalTheory.RootEx.lev 1 (σ r) =
      _root_.GlobalTheory.RootEx.lev 1 r := by
    rintro (i | i)
    · rfl
    · show _root_.GlobalTheory.RootEx.lev 1
        (_root_.GlobalTheory.StepData.stdOrd (Fin κ) t 0 l H (_root_.GlobalTheory.StepData.ixZero _ t (Sum.inr i))) = _
      rw [stdOrd_ixZero_inr]
      rfl
  have hent : ∀ r r', (_root_.GlobalTheory.StepData.Model.wt ϖ r)⁻¹ * (u : Matrix _ _ k) (σ r) (σ r') *
      _root_.GlobalTheory.StepData.Model.wt ϖ r' = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) r r' ↔
      (u : Matrix _ _ k) (σ r) (σ r') = (1 : Matrix _ _ k) (σ r) (σ r') := by
    intro r r'
    have h1 := _root_.GlobalTheory.StepData.Model.wt_ne_zero ϖ r
    have h2 := _root_.GlobalTheory.StepData.Model.wt_ne_zero ϖ r'
    by_cases h : r = r'
    · subst h
      have key : ∀ a : k, (_root_.GlobalTheory.StepData.Model.wt ϖ r)⁻¹ * a * _root_.GlobalTheory.StepData.Model.wt ϖ r = a :=
        fun a => by field_simp
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, key]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (σ.injective.ne h)]
      simp [h1, h2]
  constructor
  · intro h a b hab
    obtain ⟨r, rfl⟩ := σ.surjective a
    obtain ⟨r', rfl⟩ := σ.surjective b
    rw [hpos, hpos] at hab
    have := h r r' hab
    rw [read_apply_eq_stdOrd_mul_wt] at this
    exact (hent r r').1 this
  · intro h r r' hrr
    rw [read_apply_eq_stdOrd_mul_wt]
    exact (hent r r').2 (h _ _ (by rw [hpos, hpos]; exact hrr))
open MeasureTheory ValuativeRel Matrix Topology in
private lemma reduces_reGL_of_reduces {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) {g : GL a k} {gb : GL a 𝓀[k]} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces g gb) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces (_root_.GlobalTheory.StepData.reGL e g) (_root_.GlobalTheory.StepData.reGL e gb) := by
  obtain ⟨g₀, h1, h2⟩ := h
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] e).toAlgHom.toMonoidHom g₀, ?_, ?_⟩
  · rw [← h1]
    ext i j
    simp [_root_.GlobalTheory.StepData.reGL_val]
  · rw [← h2]
    ext i j
    simp [_root_.GlobalTheory.StepData.reGL_val]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma isUpperUnip_reGL_iff {F a b : Type} [Field F] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (e : a ≃ b) (f : b → ℕ) (g : GL a F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip f ((_root_.GlobalTheory.StepData.reGL e g : GL b F) : Matrix b b F) ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip (f ∘ e) (g : Matrix a a F) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip
  rw [_root_.GlobalTheory.StepData.reGL_val]
  constructor
  · intro h r s hrs
    have := h (e r) (e s) hrs
    simpa [Matrix.one_apply] using this
  · intro h r s hrs
    have := h (e.symm r) (e.symm s) (by simpa using hrs)
    simpa [Matrix.one_apply] using this
open MeasureTheory ValuativeRel Matrix Topology in
private lemma reGL_symm_apply {F a b : Type} [Field F] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (g : GL b F) :
    (_root_.GlobalTheory.StepData.reGL e).symm g = _root_.GlobalTheory.StepData.reGL e.symm g := by
  ext i j
  simp [_root_.GlobalTheory.StepData.reGL_symm_val, _root_.GlobalTheory.StepData.reGL_val]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma val_comp_epsEquiv_symm_eq_colPos (κ : ℕ) (t : Type) :
    (Fin.val ∘ (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t).symm) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colPos κ t := by
  funext x
  rcases x with ((i | i) | p)
  · rfl
  · exact i.elim0
  · exact p.1.elim0
open MeasureTheory ValuativeRel Matrix Topology in
private lemma superSum_submatrix_eq_superSum_comp_symm {F a b : Type} [Field F] [Fintype a] [Fintype b] (e : a ≃ b)
    (f : a → ℕ) (M : Matrix b b F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum f (M.submatrix e e) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum (f ∘ e.symm) M := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
  refine Fintype.sum_equiv e _ _ fun r => ?_
  refine Fintype.sum_equiv e _ _ fun s => ?_
  simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma simpleSum_read_eq_mul_simpleSum {k : Type} [Field k] (t : Type) [Fintype t] [DecidableEq t] {κ l : ℕ} (ϖ : kˣ)
    (H : 0 + l = l) (u : GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0 ⊕ Fin l) k) :
    _root_.GlobalTheory.RootEx.simpleSum (_root_.GlobalTheory.FirstVertexFrame.read t ϖ H u) =
      (ϖ : k) * _root_.GlobalTheory.RootEx.simpleSum u := by
  unfold _root_.GlobalTheory.RootEx.simpleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [read_apply_eq_stdOrd_mul_wt, stdOrd_ixZero_inr, stdOrd_ixZero_inr]
    have hw : ∀ m : Fin l, _root_.GlobalTheory.StepData.Model.wt (n := Fin κ) ϖ (Sum.inr m) = (ϖ : k) ^ ((m : ℕ) + 1) :=
      fun _ => rfl
    rw [hw, hw, hij]
    have := ϖ.ne_zero
    field_simp
    ring
  · simp
end GlobalTheory.FirstVertexFrame
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.FirstVertexFrame
open MeasureTheory ValuativeRel Matrix Topology
namespace GlobalTheory.FirstVertexFrame
namespace _root_.GlobalTheory.FirstVertexFrame
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t]
    (κ : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin (s + 1))),
    ((∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k,
        u * _root_.GlobalTheory.RootEx.embX (s + 1) γ ∈ P.J →
          ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val) ∧
      (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb →
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val →
          ∃ hm : _root_.GlobalTheory.RootEx.embX (s + 1) γ ∈ P.J,
            (P.lam ⟨_, hm⟩ : ℂ) =
              ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val γ.val)) ∧
      ∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) (s + 1) 1,
        ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.RootEx.simpleSum u)) →
    ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, _root_.GlobalTheory.SplitWeil.IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1),
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp
          ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J 1) :
          Set (GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) k)) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colGroup k κ t ∧
      (∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colGroup k κ t, ∃ hm : _root_.GlobalTheory.RootEx.embX c γ ∈
          ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
        (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) =
          _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colChar ψ ϖ γ) ∧
      ∀ u ∈ _root_.GlobalTheory.RootEx.N k (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) c 1,
        ∀ hm : u ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) =
            ψ (_root_.GlobalTheory.RootEx.simpleSum u) := by
  intro k _ _ _ _ ψ ϖ s t _ _ κ P hP μ hμ c H
  obtain ⟨h1, h2, h3⟩ := hP
  obtain rfl : c = s + 1 := by omega
  have hmem : ∀ x, x ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 (s + 1)
      H).J ↔
      _root_.GlobalTheory.FirstVertexFrame.read t ϖ H x ∈ P.J := by
    intro x
    unfold _root_.GlobalTheory.StepData.typeChain _root_.GlobalTheory.StepData.Chain.lev _root_.GlobalTheory.StepData.Chain.ofType
    dsimp only
    rw [_root_.GlobalTheory.StepData.Level.mem_map, _root_.GlobalTheory.StepData.TypeDatum.iter_zero]
    exact _root_.GlobalTheory.StepData.Level.mem_map
  have hlam : ∀ x (hx : x ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 (s + 1)
      H).J),
      ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 (s + 1) H).lam ⟨x, hx⟩ =
        P.lam ⟨_, (hmem x).1 hx⟩ := fun x hx => rfl
  refine ⟨?_, ?_, ?_⟩
  · ext γ
    simp only [SetLike.mem_coe, _root_.GlobalTheory.StepData.mem_prX, _root_.GlobalTheory.StepData.mem_Cgrp, inv_one,
      one_mul, mul_one]
    change _ ↔ ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colPos κ t) gb.val
    constructor
    · rintro ⟨u, hu, -, hJ⟩
      rw [hmem, map_mul, read_embX_eq_embX_reGL_symm] at hJ
      obtain ⟨gb, hr, hup⟩ := h1 _ ((read_mem_N_iff t ϖ H u).2 hu) _ hJ
      refine ⟨_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t) gb, ?_, ?_⟩
      · simpa using reduces_reGL_of_reduces (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t) hr
      · rw [isUpperUnip_reGL_iff]
        exact hup
    · rintro ⟨gb, hr, hup⟩
      refine ⟨1, one_mem _, ?_, ?_⟩
      · rw [one_mul]
        unfold _root_.GlobalTheory.RootEx.R
        exact Subgroup.mem_sup_left ⟨γ, rfl⟩
      · rw [one_mul, hmem, read_embX_eq_embX_reGL_symm]
        refine (h2 _ ((_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t)).symm gb) ?_ ?_).1
        · rw [reGL_symm_apply, reGL_symm_apply]
          exact reduces_reGL_of_reduces _ hr
        · rw [reGL_symm_apply, isUpperUnip_reGL_iff, val_comp_epsEquiv_symm_eq_colPos]
          exact hup
  · rintro γ ⟨gb, hr, hup⟩
    have hr' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces
        ((_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t)).symm γ)
        ((_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t)).symm gb) := by
      rw [reGL_symm_apply, reGL_symm_apply]
      exact reduces_reGL_of_reduces _ hr
    have hup' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val
        ((_root_.GlobalTheory.StepData.reGL (_root_.GlobalTheory.FirstVertexFrame.epsEquiv κ t)).symm gb).val := by
      rw [reGL_symm_apply, isUpperUnip_reGL_iff, val_comp_epsEquiv_symm_eq_colPos]
      exact hup
    obtain ⟨hm, hv⟩ := h2 _ _ hr' hup'
    have hm' : _root_.GlobalTheory.RootEx.embX (s + 1) γ ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 (s + 1)
        H).J := by
      rw [hmem, read_embX_eq_embX_reGL_symm]
      exact hm
    refine ⟨hm', ?_⟩
    rw [hlam]
    have he : (⟨_, (hmem _).1 hm'⟩ : P.J) = ⟨_, hm⟩ :=
      Subtype.ext (read_embX_eq_embX_reGL_symm t ϖ H γ)
    rw [he, hv]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colChar
    rw [_root_.GlobalTheory.StepData.reGL_symm_val, superSum_submatrix_eq_superSum_comp_symm, val_comp_epsEquiv_symm_eq_colPos]
  · intro u hu hm
    rw [hlam, h3 _ ((read_mem_N_iff t ϖ H u).2 hu) ((hmem u).1 hm), simpleSum_read_eq_mul_simpleSum,
      Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]
end _root_.GlobalTheory.FirstVertexFrame
end GlobalTheory.FirstVertexFrame
