-- Prove2me | solution 1 for ModularCurve.PDPairing.pairZ_nondegenerate_mod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ed44f0f9-b703-5726-b199-a2816c07c0bd

import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Schreier
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod

set_option autoImplicit false

namespace PDPairing
namespace Sat

variable {n : ℕ}

def ColProp (F : Finset (Fin n → ℤ)) : Prop :=
  (∀ f ∈ F, ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1) ∧
  (∀ i : Fin n, ∀ f ∈ F, ∀ g ∈ F, f i = 1 → g i = 1 → f = g) ∧
  (∀ i : Fin n, ∀ f ∈ F, ∀ g ∈ F, f i = -1 → g i = -1 → f = g)

theorem ColProp.mono {F G : Finset (Fin n → ℤ)} (h : G ⊆ F) (hF : ColProp F) : ColProp G :=
  ⟨fun f hf => hF.1 f (h hf),
   fun i f hf g hg => hF.2.1 i f (h hf) g (h hg),
   fun i f hf g hg => hF.2.2 i f (h hf) g (h hg)⟩

theorem ColProp.merge {F : Finset (Fin n → ℤ)} (hF : ColProp F) {p q : Fin n → ℤ}
    (hp : p ∈ F) (hq : q ∈ F) (hpq : p ≠ q) :
    ColProp (insert (p + q) ((F.erase p).erase q)) := by
  obtain ⟨h1, h2, h3⟩ := hF
  have hsub : ((F.erase p).erase q : Finset (Fin n → ℤ)) ⊆ F :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hnot2 : ∀ i, ¬(p i = 1 ∧ q i = 1) := fun i ⟨h4, h5⟩ => hpq (h2 i p hp q hq h4 h5)
  have hnotm2 : ∀ i, ¬(p i = -1 ∧ q i = -1) := fun i ⟨h4, h5⟩ => hpq (h3 i p hp q hq h4 h5)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf i
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · have hpi := h1 p hp i
      have hqi := h1 q hq i
      have hn2 := hnot2 i
      have hnm2 := hnotm2 i
      show p i + q i = -1 ∨ p i + q i = 0 ∨ p i + q i = 1
      rcases hpi with h | h | h <;> rcases hqi with h' | h' | h' <;> omega
    · exact h1 f (hsub hf') i
  · intro i f hf g hg hfi hgi
    rcases Finset.mem_insert.mp hf with rfl | hf' <;> rcases Finset.mem_insert.mp hg with rfl | hg'
    · rfl
    ·
      exfalso
      have hpi := h1 p hp i
      have hqi := h1 q hq i
      have hn2 := hnot2 i
      have : p i = 1 ∨ q i = 1 := by
        have : p i + q i = 1 := hfi
        omega
      rcases this with h | h
      · exact absurd (h2 i g (hsub hg') p hp hgi h) (by
          intro he
          have hgp : g ∈ F.erase p := Finset.mem_of_mem_erase hg'
          exact Finset.ne_of_mem_erase hgp he)
      · exact absurd (h2 i g (hsub hg') q hq hgi h) (by
          intro he
          exact Finset.notMem_erase q (F.erase p) (he ▸ hg'))
    · exfalso
      have hpi := h1 p hp i
      have hqi := h1 q hq i
      have hn2 := hnot2 i
      have : p i = 1 ∨ q i = 1 := by
        have : p i + q i = 1 := hgi
        omega
      rcases this with h | h
      · exact absurd (h2 i f (hsub hf') p hp hfi h) (by
          intro he
          have : f ∈ F.erase p := Finset.mem_of_mem_erase hf'
          exact Finset.ne_of_mem_erase this he)
      · exact absurd (h2 i f (hsub hf') q hq hfi h) (by
          intro he
          exact Finset.notMem_erase q (F.erase p) (he ▸ hf'))
    · exact h2 i f (hsub hf') g (hsub hg') hfi hgi
  · intro i f hf g hg hfi hgi
    rcases Finset.mem_insert.mp hf with rfl | hf' <;> rcases Finset.mem_insert.mp hg with rfl | hg'
    · rfl
    · exfalso
      have hpi := h1 p hp i
      have hqi := h1 q hq i
      have hnm2 := hnotm2 i
      have : p i = -1 ∨ q i = -1 := by
        have : p i + q i = -1 := hfi
        omega
      rcases this with h | h
      · exact absurd (h3 i g (hsub hg') p hp hgi h) (by
          intro he
          have : g ∈ F.erase p := Finset.mem_of_mem_erase hg'
          exact Finset.ne_of_mem_erase this he)
      · exact absurd (h3 i g (hsub hg') q hq hgi h) (by
          intro he
          exact Finset.notMem_erase q (F.erase p) (he ▸ hg'))
    · exfalso
      have hpi := h1 p hp i
      have hqi := h1 q hq i
      have hnm2 := hnotm2 i
      have : p i = -1 ∨ q i = -1 := by
        have : p i + q i = -1 := hgi
        omega
      rcases this with h | h
      · exact absurd (h3 i f (hsub hf') p hp hfi h) (by
          intro he
          have : f ∈ F.erase p := Finset.mem_of_mem_erase hf'
          exact Finset.ne_of_mem_erase this he)
      · exact absurd (h3 i f (hsub hf') q hq hfi h) (by
          intro he
          exact Finset.notMem_erase q (F.erase p) (he ▸ hf'))
    · exact h3 i f (hsub hf') g (hsub hg') hfi hgi

theorem span_saturated_of_colProp (F : Finset (Fin n → ℤ)) (hF : ColProp F)
    (v : Fin n → ℤ) (k : ℤ) (hk : k ≠ 0)
    (hv : k • v ∈ Submodule.span ℤ (F : Set (Fin n → ℤ))) :
    v ∈ Submodule.span ℤ (F : Set (Fin n → ℤ)) := by
  classical
  suffices H : ∀ (N : ℕ) (G : Finset (Fin n → ℤ)), G.card ≤ N → ColProp G →
      ∀ u : Fin n → ℤ, k • u ∈ Submodule.span ℤ (G : Set (Fin n → ℤ)) →
        u ∈ Submodule.span ℤ (G : Set (Fin n → ℤ)) by
    exact H F.card F le_rfl hF v hv
  intro N
  induction N with
  | zero =>
    intro G hcard _ u hu
    have hG : G = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hG
    rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hu ⊢
    rcases smul_eq_zero.mp hu with h | h
    · exact absurd h hk
    · exact h
  | succ N ih =>
    intro G hcard hG u hu
    by_cases hzero : ∀ f ∈ G, f = (0 : Fin n → ℤ)
    · have hle : Submodule.span ℤ (G : Set (Fin n → ℤ)) ≤ ⊥ := by
        rw [Submodule.span_le]
        intro f hf
        rw [SetLike.mem_coe, Submodule.mem_bot]
        exact hzero f hf
      have h0 : k • u = 0 := (Submodule.mem_bot ℤ).mp (hle hu)
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hk
      · rw [h]
        exact Submodule.zero_mem _
    · push Not at hzero
      obtain ⟨f₀, hf₀G, hf₀⟩ := hzero
      have hne : ∃ i₀, f₀ i₀ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hf₀ (funext fun i => hcon i)
      obtain ⟨i₀, hi₀⟩ := hne
      obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp hu
      have hread : (∑ f ∈ G, a f * f i₀) = k * u i₀ := by
        have hc := congrFun ha i₀
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc

      have hs : f₀ i₀ = 1 ∨ f₀ i₀ = -1 := by
        rcases hG.1 f₀ hf₀G i₀ with h | h | h
        · exact Or.inr h
        · exact absurd h hi₀
        · exact Or.inl h
      by_cases hpair : ∃ g₀ ∈ G, g₀ i₀ = -(f₀ i₀)
      ·
        obtain ⟨g₀, hg₀G, hg₀⟩ := hpair

        obtain ⟨p, q, hpG, hqG, hp1, hq1⟩ :
            ∃ p q, p ∈ G ∧ q ∈ G ∧ p i₀ = 1 ∧ q i₀ = -1 := by
          rcases hs with h | h
          · exact ⟨f₀, g₀, hf₀G, hg₀G, h, by rw [hg₀, h]⟩
          · exact ⟨g₀, f₀, hg₀G, hf₀G, (by rw [hg₀, h]; norm_num), h⟩
        have hpq : p ≠ q := fun he => by
          rw [he, hq1] at hp1
          exact absurd hp1 (by norm_num)
        have hqe : q ∈ G.erase p := Finset.mem_erase.mpr ⟨fun he => hpq he.symm, hqG⟩

        have hothers : ∀ f ∈ (G.erase p).erase q, f i₀ = 0 := by
          intro f hf
          have hfG : f ∈ G := (Finset.erase_subset _ _) ((Finset.erase_subset _ _) hf)
          rcases hG.1 f hfG i₀ with h | h | h
          · exact absurd (hG.2.2 i₀ f hfG q hqG h hq1)
              (Finset.ne_of_mem_erase hf)
          · exact h
          · exact absurd (hG.2.1 i₀ f hfG p hpG h hp1)
              (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hf))
        have hsplit : (∑ f ∈ G, a f • f)
            = a p • p + a q • q + ∑ f ∈ (G.erase p).erase q, a f • f := by
          rw [← Finset.sum_erase_add G _ hpG, ← Finset.sum_erase_add (G.erase p) _ hqe]
          abel
        have hreadpq : a p - a q = k * u i₀ := by
          have hc := congrFun hsplit i₀
          rw [ha] at hc
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hc
          rw [hp1, hq1] at hc
          have hz : (∑ f ∈ (G.erase p).erase q, a f * f i₀) = 0 :=
            Finset.sum_eq_zero fun f hf => by rw [hothers f hf, mul_zero]
          rw [hz] at hc
          have : k * u i₀ = a p * 1 + a q * (-1) + 0 := hc
          linarith

        set G' : Finset (Fin n → ℤ) := insert (p + q) ((G.erase p).erase q) with hG'
        set u' : Fin n → ℤ := u - (u i₀) • p with hu'
        have hcard' : G'.card ≤ N := by
          have h1 : ((G.erase p).erase q).card = G.card - 2 := by
            rw [Finset.card_erase_of_mem hqe, Finset.card_erase_of_mem hpG]
            omega
          have h2 : G'.card ≤ ((G.erase p).erase q).card + 1 := Finset.card_insert_le _ _
          have h3 : 2 ≤ G.card := Finset.one_lt_card.mpr ⟨p, hpG, q, hqG, hpq⟩
          omega
        have hcol' : ColProp G' := hG.merge hpG hqG hpq
        have hku' : k • u' ∈ Submodule.span ℤ (G' : Set (Fin n → ℤ)) := by
          have hap : a p = a q + k * u i₀ := by linarith
          have hexpr : k • u' = a q • (p + q) + ∑ f ∈ (G.erase p).erase q, a f • f := by
            rw [hu', smul_sub, smul_smul, ← ha, hsplit, hap, add_smul, smul_add]
            abel
          rw [hexpr]
          refine Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (by
              rw [hG']
              exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))) ?_
          refine Submodule.sum_mem _ fun f hf => Submodule.smul_mem _ _ (Submodule.subset_span (by
            rw [hG']
            exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hf)))
        have hrec := ih G' hcard' hcol' u' hku'
        have hspan' : Submodule.span ℤ (G' : Set (Fin n → ℤ))
            ≤ Submodule.span ℤ (G : Set (Fin n → ℤ)) := by
          rw [Submodule.span_le, hG']
          intro x hx
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with h | h
          · rw [h]
            exact Submodule.add_mem _ (Submodule.subset_span hpG) (Submodule.subset_span hqG)
          · exact Submodule.subset_span
              ((Finset.erase_subset _ _) ((Finset.erase_subset _ _) h))
        have hfin : u = u' + (u i₀) • p := by
          rw [hu']
          abel
        rw [hfin]
        exact Submodule.add_mem _ (hspan' hrec)
          (Submodule.smul_mem _ _ (Submodule.subset_span hpG))
      ·
        push Not at hpair
        have hothers : ∀ f ∈ G.erase f₀, f i₀ = 0 := by
          intro f hf
          have hfG : f ∈ G := Finset.erase_subset _ _ hf
          have hne' : f ≠ f₀ := Finset.ne_of_mem_erase hf
          rcases hG.1 f hfG i₀ with h | h | h
          · rcases hs with h' | h'
            · exact absurd (by rw [h, h']) (hpair f hfG)
            · exact absurd (hG.2.2 i₀ f hfG f₀ hf₀G h h') hne'
          · exact h
          · rcases hs with h' | h'
            · exact absurd (hG.2.1 i₀ f hfG f₀ hf₀G h h') hne'
            · exact absurd (by rw [h, h']; norm_num) (hpair f hfG)
        have hsplit : (∑ f ∈ G, a f • f) = a f₀ • f₀ + ∑ f ∈ G.erase f₀, a f • f := by
          rw [← Finset.sum_erase_add G _ hf₀G]
          abel
        have hread0 : a f₀ * f₀ i₀ = k * u i₀ := by
          have hc := congrFun hsplit i₀
          rw [ha] at hc
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hc
          have hz : (∑ f ∈ G.erase f₀, a f * f i₀) = 0 :=
            Finset.sum_eq_zero fun f hf => by rw [hothers f hf, mul_zero]
          rw [hz] at hc
          linarith
        set s : ℤ := f₀ i₀ with hsdef
        have haf₀ : a f₀ = s * (k * u i₀) := by
          have h := hread0
          rcases hs with h' | h' <;> rw [h'] at h ⊢ <;> linarith
        set u' : Fin n → ℤ := u - (s * u i₀) • f₀ with hu'
        have hku' : k • u' ∈ Submodule.span ℤ ((G.erase f₀ : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := by
          have hscal : k * (s * u i₀) = a f₀ := by
            rw [haf₀]
            ring
          have hexpr : k • u' = ∑ f ∈ G.erase f₀, a f • f := by
            rw [hu', smul_sub, smul_smul, ← ha, hsplit, hscal]
            abel
          rw [hexpr]
          exact Submodule.sum_mem _ fun f hf =>
            Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr hf))
        have hcard' : (G.erase f₀).card ≤ N := by
          rw [Finset.card_erase_of_mem hf₀G]
          omega
        have hrec := ih (G.erase f₀) hcard' (hG.mono (Finset.erase_subset _ _)) u' hku'
        have hspan' : Submodule.span ℤ ((G.erase f₀ : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))
            ≤ Submodule.span ℤ (G : Set (Fin n → ℤ)) :=
          Submodule.span_mono (by
            intro x hx
            exact Finset.mem_coe.mpr (Finset.erase_subset _ _ (Finset.mem_coe.mp hx)))
        have hfin : u = u' + (s * u i₀) • f₀ := by
          rw [hu']
          abel
        rw [hfin]
        exact Submodule.add_mem _ (hspan' hrec)
          (Submodule.smul_mem _ _ (Submodule.subset_span hf₀G))

end PDPairing.Sat

namespace PDPairing
namespace Chord

private structure _root_.PDPairing.Chord.ChordDiagram (n : ℕ) where
  dart : (Fin n) ⊕ (Fin n) ≃ Fin (2 * n)

p2m_export "PDPairing.Chord" "ChordDiagram"
p2m_export_all "PDPairing.Chord" "ChordDiagram"
namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

private def _root_.PDPairing.Chord.ChordDiagram.pos (i : Fin n) : Fin (2 * n) := D.dart (Sum.inl i)

p2m_export "PDPairing.Chord.ChordDiagram" "pos"
private def _root_.PDPairing.Chord.ChordDiagram.neg (i : Fin n) : Fin (2 * n) := D.dart (Sum.inr i)

p2m_export "PDPairing.Chord.ChordDiagram" "neg"
private def _root_.PDPairing.Chord.ChordDiagram.cdist (a x : Fin (2 * n)) : ℕ := (x.val + 2 * n - a.val) % (2 * n)

p2m_export "PDPairing.Chord.ChordDiagram" "cdist"
private def _root_.PDPairing.Chord.ChordDiagram.ArcMem (a b p : Fin (2 * n)) : Prop := 0 < cdist a p ∧ cdist a p < cdist a b

p2m_export "PDPairing.Chord.ChordDiagram" "ArcMem"
scoped instance (a b p : Fin (2 * n)) : Decidable (ArcMem a b p) := by
  unfold ArcMem; infer_instance

private def _root_.PDPairing.Chord.ChordDiagram.eps (i j : Fin n) : ℤ :=
  (if ArcMem (D.pos i) (D.neg i) (D.pos j) then 1 else 0)
    - (if ArcMem (D.pos i) (D.neg i) (D.neg j) then 1 else 0)

p2m_export "PDPairing.Chord.ChordDiagram" "eps"
private def _root_.PDPairing.Chord.ChordDiagram.partner : Equiv.Perm (Fin (2 * n)) :=
  (D.dart.symm.trans (Equiv.sumComm (Fin n) (Fin n))).trans D.dart

p2m_export "PDPairing.Chord.ChordDiagram" "partner"
private def _root_.PDPairing.Chord.ChordDiagram.facePerm : Equiv.Perm (Fin (2 * n)) := D.partner.trans (finRotate (2 * n))

p2m_export "PDPairing.Chord.ChordDiagram" "facePerm"
private def _root_.PDPairing.Chord.ChordDiagram.dartVec (p : Fin (2 * n)) : Fin n → ℤ :=
  Sum.elim (fun i => Pi.single i (1 : ℤ)) (fun i => Pi.single i (-1 : ℤ)) (D.dart.symm p)

p2m_export "PDPairing.Chord.ChordDiagram" "dartVec"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceVecAt (p : Fin (2 * n)) : Fin n → ℤ :=
  ∑ k ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p), D.dartVec ((D.facePerm ^ k) p)

p2m_export "PDPairing.Chord.ChordDiagram" "faceVecAt"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceLattice : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range D.faceVecAt)

p2m_export "PDPairing.Chord.ChordDiagram" "faceLattice"
private abbrev _root_.PDPairing.Chord.ChordDiagram.ParQuot : Type := (Fin n → ℤ) ⧸ D.faceLattice

p2m_export "PDPairing.Chord.ChordDiagram" "ParQuot"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.epsForm : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => ∑ i, ∑ j, v i * D.eps i j * w j)
    (by
      intro v v' w
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by
      intro c v w
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (by
      intro v w w'
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro c v w
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

p2m_export "PDPairing.Chord.ChordDiagram" "epsForm"
private theorem _root_.PDPairing.Chord.ChordDiagram.cdist_self (a : Fin (2 * n)) : cdist a a = 0 := by
  unfold cdist
  have h : a.val + 2 * n - a.val = 2 * n := by omega
  rw [h, Nat.mod_self]

p2m_export "PDPairing.Chord.ChordDiagram" "cdist_self"
private theorem _root_.PDPairing.Chord.ChordDiagram.cdist_spec (a x : Fin (2 * n)) :
    (a.val ≤ x.val ∧ cdist a x = x.val - a.val) ∨
      (x.val < a.val ∧ cdist a x = x.val + 2 * n - a.val) := by
  have hx := x.isLt
  have ha := a.isLt
  rcases Nat.lt_or_ge x.val a.val with h | h
  · right
    refine ⟨h, ?_⟩
    unfold cdist
    exact Nat.mod_eq_of_lt (by omega)
  · left
    refine ⟨h, ?_⟩
    unfold cdist
    have h2 : x.val + 2 * n - a.val = (x.val - a.val) + 2 * n := by omega
    rw [h2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

p2m_export "PDPairing.Chord.ChordDiagram" "cdist_spec"
private theorem _root_.PDPairing.Chord.ChordDiagram.pos_injective : Function.Injective D.pos := fun _ _ h =>
  Sum.inl_injective (D.dart.injective h)

p2m_export "PDPairing.Chord.ChordDiagram" "pos_injective"
private theorem _root_.PDPairing.Chord.ChordDiagram.neg_injective : Function.Injective D.neg := fun _ _ h =>
  Sum.inr_injective (D.dart.injective h)

p2m_export "PDPairing.Chord.ChordDiagram" "neg_injective"
private theorem _root_.PDPairing.Chord.ChordDiagram.pos_ne_neg (i j : Fin n) : D.pos i ≠ D.neg j := fun h =>
  Sum.inl_ne_inr (D.dart.injective h)

p2m_export "PDPairing.Chord.ChordDiagram" "pos_ne_neg"
set_option maxHeartbeats 1600000 in
private theorem _root_.PDPairing.Chord.ChordDiagram.eps_skew (i j : Fin n) : D.eps j i = -D.eps i j := by
  rcases eq_or_ne i j with rfl | hij
  · unfold eps ArcMem
    simp [cdist_self]
  · have d1 : (D.pos i).val ≠ (D.neg i).val := fun h => D.pos_ne_neg i i (Fin.ext h)
    have d2 : (D.pos j).val ≠ (D.neg j).val := fun h => D.pos_ne_neg j j (Fin.ext h)
    have d3 : (D.pos i).val ≠ (D.pos j).val := fun h => hij (D.pos_injective (Fin.ext h))
    have d4 : (D.pos i).val ≠ (D.neg j).val := fun h => D.pos_ne_neg i j (Fin.ext h)
    have d5 : (D.pos j).val ≠ (D.neg i).val := fun h => D.pos_ne_neg j i (Fin.ext h)
    have d6 : (D.neg i).val ≠ (D.neg j).val := fun h => hij (D.neg_injective (Fin.ext h))
    have s1 := cdist_spec (D.pos i) (D.neg i)
    have s2 := cdist_spec (D.pos i) (D.pos j)
    have s3 := cdist_spec (D.pos i) (D.neg j)
    have s4 := cdist_spec (D.pos j) (D.neg j)
    have s5 := cdist_spec (D.pos j) (D.pos i)
    have s6 := cdist_spec (D.pos j) (D.neg i)
    unfold eps ArcMem
    split_ifs <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "eps_skew"
private theorem _root_.PDPairing.Chord.ChordDiagram.arc_step (a b q : Fin (2 * n)) (hab : a ≠ b) :
    (cdist b q : ℤ) - cdist a q + cdist a b
      = 2 * n * ((if ArcMem a b q then 1 else 0) + (if q = a then 1 else 0)) := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have s1 := cdist_spec b q
  have s2 := cdist_spec a q
  have s3 := cdist_spec a b
  unfold ArcMem
  have hq : q = a ↔ q.val = a.val := ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  simp only [hq]
  split_ifs <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "arc_step"
private theorem _root_.PDPairing.Chord.ChordDiagram.cdist_rotate (y : Fin (2 * n)) : cdist y ((finRotate (2 * n)) y) = 1 := by
  haveI := y.neZero
  have hy := y.isLt
  have h2 : 2 ≤ 2 * n := by omega
  have hone : ((1 : Fin (2 * n))).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  rw [finRotate_apply]
  have hval : ((y + 1 : Fin (2 * n))).val = (y.val + 1) % (2 * n) := by
    rw [Fin.val_add, hone]
  unfold cdist
  rw [hval]
  rcases Nat.lt_or_ge (y.val + 1) (2 * n) with h | h
  · rw [Nat.mod_eq_of_lt h]
    have he : y.val + 1 + 2 * n - y.val = 1 + 2 * n := by omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · have hy1 : y.val + 1 = 2 * n := by omega
    rw [hy1, Nat.mod_self]
    have he : 0 + 2 * n - y.val = 1 := by omega
    rw [he]
    exact Nat.mod_eq_of_lt (by omega)

p2m_export "PDPairing.Chord.ChordDiagram" "cdist_rotate"
private theorem _root_.PDPairing.Chord.ChordDiagram.arcMem_rotate_false (y q : Fin (2 * n)) : ¬ArcMem y ((finRotate (2 * n)) y) q := by
  intro hmem
  rcases hmem with ⟨hpos, hlt⟩
  rw [cdist_rotate] at hlt
  omega

p2m_export "PDPairing.Chord.ChordDiagram" "arcMem_rotate_false"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_pos (i : Fin n) : D.partner (D.pos i) = D.neg i := by
  simp [partner, pos, neg]

p2m_export "PDPairing.Chord.ChordDiagram" "partner_pos"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_neg (i : Fin n) : D.partner (D.neg i) = D.pos i := by
  simp [partner, pos, neg]

p2m_export "PDPairing.Chord.ChordDiagram" "partner_neg"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_partner (d : Fin (2 * n)) : D.partner (D.partner d) = d := by
  simp [partner]

p2m_export "PDPairing.Chord.ChordDiagram" "partner_partner"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_ne_self (d : Fin (2 * n)) : D.partner d ≠ d := by
  rcases h : D.dart.symm d with c | c
  · have hd : d = D.pos c := by rw [pos, ← h, Equiv.apply_symm_apply]
    rw [hd, partner_pos]
    exact fun hh => D.pos_ne_neg c c hh.symm
  · have hd : d = D.neg c := by rw [neg, ← h, Equiv.apply_symm_apply]
    rw [hd, partner_neg]
    exact D.pos_ne_neg c c

p2m_export "PDPairing.Chord.ChordDiagram" "partner_ne_self"
private theorem _root_.PDPairing.Chord.ChordDiagram.perm_pow_apply (σ : Equiv.Perm (Fin (2 * n))) (k : ℕ) (y : Fin (2 * n)) :
    (σ ^ k) y = (⇑σ)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    show σ ((σ ^ k) y) = _
    rw [ih]

p2m_export "PDPairing.Chord.ChordDiagram" "perm_pow_apply"
private theorem _root_.PDPairing.Chord.ChordDiagram.facePerm_apply (d : Fin (2 * n)) :
    D.facePerm d = (finRotate (2 * n)) (D.partner d) := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "facePerm_apply"
private theorem _root_.PDPairing.Chord.ChordDiagram.walk_diff (p P : Fin (2 * n)) :
    ∑ k ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      ((if ArcMem ((D.facePerm ^ k) p) (D.partner ((D.facePerm ^ k) p)) P then (1 : ℤ) else 0)
        - (if ArcMem ((D.facePerm ^ k) p) (D.partner ((D.facePerm ^ k) p)) (D.partner P)
            then (1 : ℤ) else 0)) = 0 := by
  classical
  have h2n : 0 < 2 * n := p.pos
  set m := Function.minimalPeriod (⇑D.facePerm) p with hm
  set N := D.partner P with hN
  set x : ℕ → Fin (2 * n) := fun k => (D.facePerm ^ k) p with hx
  set g : ℕ → ℤ := fun k => (cdist (x k) P : ℤ) - cdist (x k) N with hg
  have hxsucc : ∀ k, x (k + 1) = (finRotate (2 * n)) (D.partner (x k)) := by
    intro k
    show (D.facePerm ^ (k + 1)) p = _
    rw [pow_succ']
    rfl
  have key : ∀ k, (2 * (n : ℤ)) *
      ((if ArcMem (x k) (D.partner (x k)) P then (1 : ℤ) else 0)
        - (if ArcMem (x k) (D.partner (x k)) N then (1 : ℤ) else 0))
      = g (k + 1) - g k := by
    intro k
    have hxy : x k ≠ D.partner (x k) := fun h => D.partner_ne_self (x k) h.symm
    have hyz : D.partner (x k) ≠ (finRotate (2 * n)) (D.partner (x k)) := by
      intro h
      have h1 := cdist_rotate (D.partner (x k))
      rw [← h, cdist_self] at h1
      exact one_ne_zero h1.symm
    have hiff1 : P = D.partner (x k) ↔ N = x k := by
      rw [hN]
      constructor
      · intro h
        rw [h, partner_partner]
      · intro h
        rw [← h, partner_partner]
    have hiff2 : N = D.partner (x k) ↔ P = x k := by
      rw [hN]
      constructor
      · intro h
        exact D.partner.injective h
      · intro h
        rw [h]
    have j1 : (if P = D.partner (x k) then (1 : ℤ) else 0)
        = (if N = x k then (1 : ℤ) else 0) := by
      by_cases h : N = x k
      · rw [if_pos (hiff1.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff1.mp hh)), if_neg h]
    have j2 : (if N = D.partner (x k) then (1 : ℤ) else 0)
        = (if P = x k then (1 : ℤ) else 0) := by
      by_cases h : P = x k
      · rw [if_pos (hiff2.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff2.mp hh)), if_neg h]
    have hA1 := arc_step (x k) (D.partner (x k)) P hxy
    have hA2 := arc_step (x k) (D.partner (x k)) N hxy
    have hB1 := arc_step (D.partner (x k)) ((finRotate (2 * n)) (D.partner (x k))) P hyz
    have hB2 := arc_step (D.partner (x k)) ((finRotate (2 * n)) (D.partner (x k))) N hyz
    rw [if_neg (arcMem_rotate_false (D.partner (x k)) P)] at hB1
    rw [if_neg (arcMem_rotate_false (D.partner (x k)) N)] at hB2
    rw [j1] at hB1
    rw [j2] at hB2
    rw [← hxsucc k] at hB1 hB2
    have hg1 : g (k + 1) = (cdist (x (k + 1)) P : ℤ) - cdist (x (k + 1)) N := rfl
    have hg0 : g k = (cdist (x k) P : ℤ) - cdist (x k) N := rfl
    rw [hg1, hg0]
    split_ifs at hA1 hA2 hB1 hB2 ⊢ <;> omega
  have hsum : ∑ k ∈ Finset.range m,
      ((2 * (n : ℤ)) * ((if ArcMem (x k) (D.partner (x k)) P then (1 : ℤ) else 0)
        - (if ArcMem (x k) (D.partner (x k)) N then (1 : ℤ) else 0)))
      = g m - g 0 := by
    rw [Finset.sum_congr rfl fun k _ => key k]
    exact Finset.sum_range_sub g m
  have hclosed : x m = x 0 := by
    show (D.facePerm ^ m) p = (D.facePerm ^ 0) p
    rw [perm_pow_apply, perm_pow_apply, hm]
    rw [Function.iterate_minimalPeriod]
    rfl
  rw [← Finset.mul_sum] at hsum
  have hg_eq : g m = g 0 := by rw [hg]; simp only [hclosed]
  rw [hg_eq, sub_self] at hsum
  have h2nz : (2 * (n : ℤ)) ≠ 0 := by
    have : (0 : ℤ) < 2 * n := by exact_mod_cast h2n
    omega
  exact (mul_eq_zero.mp hsum).resolve_left h2nz

p2m_export "PDPairing.Chord.ChordDiagram" "walk_diff"
private theorem _root_.PDPairing.Chord.ChordDiagram.step_diff (q P : Fin (2 * n)) :
    (2 * (n : ℤ)) * ((if ArcMem q (D.partner q) P then (1 : ℤ) else 0)
        - (if ArcMem q (D.partner q) (D.partner P) then (1 : ℤ) else 0))
      = (((cdist (D.facePerm q) P : ℤ) - cdist (D.facePerm q) (D.partner P))
        - ((cdist q P : ℤ) - cdist q (D.partner P))) := by
  classical
  set N := D.partner P with hN
  have hxy : q ≠ D.partner q := fun h => D.partner_ne_self q h.symm
  have hyz : D.partner q ≠ (finRotate (2 * n)) (D.partner q) := by
    intro h
    have h1 := cdist_rotate (D.partner q)
    rw [← h, cdist_self] at h1
    exact one_ne_zero h1.symm
  have hiff1 : P = D.partner q ↔ N = q := by
    rw [hN]
    constructor
    · intro h
      rw [h, partner_partner]
    · intro h
      rw [← h, partner_partner]
  have hiff2 : N = D.partner q ↔ P = q := by
    rw [hN]
    constructor
    · intro h
      exact D.partner.injective h
    · intro h
      rw [h]
  have j1 : (if P = D.partner q then (1 : ℤ) else 0) = (if N = q then (1 : ℤ) else 0) := by
    by_cases h : N = q
    · rw [if_pos (hiff1.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hiff1.mp hh)), if_neg h]
  have j2 : (if N = D.partner q then (1 : ℤ) else 0) = (if P = q then (1 : ℤ) else 0) := by
    by_cases h : P = q
    · rw [if_pos (hiff2.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hiff2.mp hh)), if_neg h]
  have hA1 := arc_step q (D.partner q) P hxy
  have hA2 := arc_step q (D.partner q) N hxy
  have hB1 := arc_step (D.partner q) ((finRotate (2 * n)) (D.partner q)) P hyz
  have hB2 := arc_step (D.partner q) ((finRotate (2 * n)) (D.partner q)) N hyz
  rw [if_neg (arcMem_rotate_false (D.partner q) P)] at hB1
  rw [if_neg (arcMem_rotate_false (D.partner q) N)] at hB2
  rw [j1] at hB1
  rw [j2] at hB2
  rw [← D.facePerm_apply q] at hB1 hB2
  split_ifs at hA1 hA2 hB1 hB2 ⊢ <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "step_diff"
private theorem _root_.PDPairing.Chord.ChordDiagram.rotate_phi (e P : Fin (2 * n)) :
    (((cdist ((finRotate (2 * n)) e) P : ℤ) - cdist ((finRotate (2 * n)) e) (D.partner P))
        - ((cdist e P : ℤ) - cdist e (D.partner P)))
      = (2 * (n : ℤ)) * ((if P = e then (1 : ℤ) else 0)
          - (if D.partner P = e then (1 : ℤ) else 0)) := by
  classical
  have hez : e ≠ (finRotate (2 * n)) e := by
    intro h
    have h1 := cdist_rotate e
    rw [← h, cdist_self] at h1
    exact one_ne_zero h1.symm
  have hB1 := arc_step e ((finRotate (2 * n)) e) P hez
  have hB2 := arc_step e ((finRotate (2 * n)) e) (D.partner P) hez
  rw [if_neg (arcMem_rotate_false e P)] at hB1
  rw [if_neg (arcMem_rotate_false e (D.partner P))] at hB2
  split_ifs at hB1 hB2 ⊢ <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "rotate_phi"
private theorem _root_.PDPairing.Chord.ChordDiagram.arcMem_swap_ite (a b q : Fin (2 * n)) (hab : a ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    (if ArcMem b a q then (1 : ℤ) else 0) = 1 - (if ArcMem a b q then (1 : ℤ) else 0) := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hqa' : q.val ≠ a.val := fun h => hqa (Fin.ext h)
  have hqb' : q.val ≠ b.val := fun h => hqb (Fin.ext h)
  have s1 := cdist_spec b a
  have s2 := cdist_spec b q
  have s3 := cdist_spec a b
  have s4 := cdist_spec a q
  unfold ArcMem
  split_ifs <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "arcMem_swap_ite"
private theorem _root_.PDPairing.Chord.ChordDiagram.dart_collapse (d : Fin (2 * n)) (j : Fin n) :
    (∑ i, D.dartVec d i * D.eps i j)
      = (if ArcMem d (D.partner d) (D.pos j) then (1 : ℤ) else 0)
        - (if ArcMem d (D.partner d) (D.neg j) then (1 : ℤ) else 0) := by
  classical
  rcases hsym : D.dart.symm d with c | c
  · have hd : d = D.pos c := by rw [pos, ← hsym, Equiv.apply_symm_apply]
    have hdv : D.dartVec d = Pi.single c (1 : ℤ) := by
      rw [dartVec, hsym]
      rfl
    have hsum : (∑ i, D.dartVec d i * D.eps i j) = D.eps c j := by
      rw [hdv]
      simp [Pi.single_apply, ite_mul, zero_mul]
    rw [hsum, hd, partner_pos]
    rfl
  · have hd : d = D.neg c := by rw [neg, ← hsym, Equiv.apply_symm_apply]
    have hdv : D.dartVec d = Pi.single c (-1 : ℤ) := by
      rw [dartVec, hsym]
      rfl
    have hsum : (∑ i, D.dartVec d i * D.eps i j) = -D.eps c j := by
      rw [hdv]
      simp [Pi.single_apply, ite_mul, zero_mul]
    rw [hsum, hd, partner_neg]
    rcases eq_or_ne c j with rfl | hcj
    · have h1 : ¬ArcMem (D.neg c) (D.pos c) (D.pos c) := fun h => absurd h.2 (lt_irrefl _)
      have h2 : ¬ArcMem (D.neg c) (D.pos c) (D.neg c) := fun h => by
        have hp := h.1
        rw [cdist_self] at hp
        exact absurd hp (lt_irrefl 0)
      have h3 : ¬ArcMem (D.pos c) (D.neg c) (D.pos c) := fun h => by
        have hp := h.1
        rw [cdist_self] at hp
        exact absurd hp (lt_irrefl 0)
      have h4 : ¬ArcMem (D.pos c) (D.neg c) (D.neg c) := fun h => absurd h.2 (lt_irrefl _)
      rw [if_neg h1, if_neg h2]
      show -D.eps c c = 0 - 0
      unfold eps
      rw [if_neg h3, if_neg h4]
      ring
    · have hqa1 : D.pos j ≠ D.neg c := (D.pos_ne_neg j c)
      have hqb1 : D.pos j ≠ D.pos c := fun h => hcj (D.pos_injective h.symm)
      have hqa2 : D.neg j ≠ D.neg c := fun h => hcj (D.neg_injective h.symm)
      have hqb2 : D.neg j ≠ D.pos c := (D.pos_ne_neg c j).symm
      have hab : D.pos c ≠ D.neg c := D.pos_ne_neg c c
      rw [arcMem_swap_ite (D.pos c) (D.neg c) (D.pos j) hab hqb1 hqa1,
        arcMem_swap_ite (D.pos c) (D.neg c) (D.neg j) hab hqb2 hqa2]
      unfold eps
      ring

p2m_export "PDPairing.Chord.ChordDiagram" "dart_collapse"
private theorem _root_.PDPairing.Chord.ChordDiagram.epsForm_faceVecAt (p : Fin (2 * n)) (w : Fin n → ℤ) :
    D.epsForm (D.faceVecAt p) w = 0 := by
  classical
  suffices hrow : ∀ j, (∑ i, D.faceVecAt p i * D.eps i j) = 0 by
    show (∑ i, ∑ j, D.faceVecAt p i * D.eps i j * w j) = 0
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, hrow j, zero_mul]
  intro j
  have hexp : (∑ i, D.faceVecAt p i * D.eps i j)
      = ∑ k ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          (∑ i, D.dartVec ((D.facePerm ^ k) p) i * D.eps i j) := by
    simp only [faceVecAt, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hexp]
  rw [Finset.sum_congr rfl fun k _ => D.dart_collapse ((D.facePerm ^ k) p) j]
  have hwd := D.walk_diff p (D.pos j)
  rw [D.partner_pos j] at hwd
  exact hwd

p2m_export "PDPairing.Chord.ChordDiagram" "epsForm_faceVecAt"
private theorem _root_.PDPairing.Chord.ChordDiagram.epsForm_faceVecAt_right (v : Fin n → ℤ) (p : Fin (2 * n)) :
    D.epsForm v (D.faceVecAt p) = 0 := by
  have hL : D.epsForm (D.faceVecAt p) v = 0 := D.epsForm_faceVecAt p v
  have hswap : D.epsForm v (D.faceVecAt p) = -D.epsForm (D.faceVecAt p) v := by
    show (∑ i, ∑ j, v i * D.eps i j * D.faceVecAt p j)
        = -(∑ i, ∑ j, D.faceVecAt p i * D.eps i j * v j)
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [D.eps_skew j i]
    ring
  rw [hswap, hL, neg_zero]

p2m_export "PDPairing.Chord.ChordDiagram" "epsForm_faceVecAt_right"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceLattice_le_ker : D.faceLattice ≤ LinearMap.ker D.epsForm := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.zero_apply]
  exact D.epsForm_faceVecAt p w

p2m_export "PDPairing.Chord.ChordDiagram" "faceLattice_le_ker"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.epsFormQright (v : Fin n → ℤ) : D.ParQuot →ₗ[ℤ] ℤ :=
  D.faceLattice.liftQ (D.epsForm v)
    (by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact D.epsForm_faceVecAt_right v p)

p2m_export "PDPairing.Chord.ChordDiagram" "epsFormQright"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.epsFormQ : D.ParQuot →ₗ[ℤ] D.ParQuot →ₗ[ℤ] ℤ :=
  D.faceLattice.liftQ
    { toFun := fun v => D.epsFormQright v
      map_add' := by
        intro v v'
        refine LinearMap.ext fun q => ?_
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show D.epsForm (v + v') w = D.epsForm v w + D.epsForm v' w
        rw [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c v
        refine LinearMap.ext fun q => ?_
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show D.epsForm (c • v) w = c • D.epsForm v w
        rw [map_smul, LinearMap.smul_apply] }
    (by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      refine LinearMap.ext fun q => ?_
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show D.epsForm (D.faceVecAt p) w = 0
      exact D.epsForm_faceVecAt p w)

p2m_export "PDPairing.Chord.ChordDiagram" "epsFormQ"
private theorem _root_.PDPairing.Chord.ChordDiagram.mem_periodicPts_facePerm (p : Fin (2 * n)) :
    p ∈ Function.periodicPts ⇑D.facePerm := by
  refine ⟨orderOf D.facePerm, orderOf_pos _, ?_⟩
  show Function.IsPeriodicPt _ _ _
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← perm_pow_apply, pow_orderOf_eq_one]
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "mem_periodicPts_facePerm"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.orbitFinset (p : Fin (2 * n)) : Finset (Fin (2 * n)) :=
  (Finset.range (Function.minimalPeriod (⇑D.facePerm) p)).image (fun k => (D.facePerm ^ k) p)

p2m_export "PDPairing.Chord.ChordDiagram" "orbitFinset"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceVecAt_eq_orbit_sum (p : Fin (2 * n)) :
    D.faceVecAt p = ∑ d ∈ D.orbitFinset p, D.dartVec d := by
  rw [faceVecAt, orbitFinset, Finset.sum_image]
  intro a ha b hb hab
  have ha' : a < Function.minimalPeriod (⇑D.facePerm) p := by simpa using ha
  have hb' : b < Function.minimalPeriod (⇑D.facePerm) p := by simpa using hb
  have hab' : (⇑D.facePerm)^[a] p = (⇑D.facePerm)^[b] p := by
    have h := hab
    simp only [] at h
    rw [perm_pow_apply, perm_pow_apply] at h
    exact h
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Set.mem_Iio.mpr ha') (Set.mem_Iio.mpr hb') hab'

p2m_export "PDPairing.Chord.ChordDiagram" "faceVecAt_eq_orbit_sum"
private theorem _root_.PDPairing.Chord.ChordDiagram.mem_orbitFinset_self (p : Fin (2 * n)) : p ∈ D.orbitFinset p :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr
    (Function.minimalPeriod_pos_of_mem_periodicPts (D.mem_periodicPts_facePerm p)), by simp⟩

p2m_export "PDPairing.Chord.ChordDiagram" "mem_orbitFinset_self"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitFinset_apply (p : Fin (2 * n)) :
    D.orbitFinset (D.facePerm p) = D.orbitFinset p := by
  have hm := Function.minimalPeriod_apply (D.mem_periodicPts_facePerm p)
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts (D.mem_periodicPts_facePerm p)
  set m := Function.minimalPeriod (⇑D.facePerm) p with hmdef
  ext x
  simp only [orbitFinset, Finset.mem_image, Finset.mem_range, hm]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k + 1) % m, Nat.mod_lt _ hpos, ?_⟩
    rw [perm_pow_apply, perm_pow_apply, Function.iterate_mod_minimalPeriod_eq,
      Function.iterate_succ_apply]
  · rintro ⟨k, hk, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨m - 1, by omega, ?_⟩
      rw [perm_pow_apply, perm_pow_apply, ← Function.iterate_succ_apply,
        Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      show (⇑D.facePerm)^[m] p = (⇑D.facePerm)^[0] p
      rw [hmdef, Function.iterate_minimalPeriod]
      rfl
    · refine ⟨k - 1, by omega, ?_⟩
      rw [perm_pow_apply, perm_pow_apply, ← Function.iterate_succ_apply,
        Nat.succ_eq_add_one, Nat.sub_add_cancel hk0]

p2m_export "PDPairing.Chord.ChordDiagram" "orbitFinset_apply"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitFinset_pow_apply (p : Fin (2 * n)) (j : ℕ) :
    D.orbitFinset ((D.facePerm ^ j) p) = D.orbitFinset p := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : (D.facePerm ^ (j + 1)) p = D.facePerm ((D.facePerm ^ j) p) := by
      rw [pow_succ']
      rfl
    rw [hstep, orbitFinset_apply, ih]

p2m_export "PDPairing.Chord.ChordDiagram" "orbitFinset_pow_apply"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceVecAt_eq_of_mem {p d : Fin (2 * n)} (hd : d ∈ D.orbitFinset p) :
    D.faceVecAt d = D.faceVecAt p := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hd
  rw [faceVecAt_eq_orbit_sum, faceVecAt_eq_orbit_sum, orbitFinset_pow_apply]

p2m_export "PDPairing.Chord.ChordDiagram" "faceVecAt_eq_of_mem"
private theorem _root_.PDPairing.Chord.ChordDiagram.dartVec_apply_eq (d : Fin (2 * n)) (i : Fin n) :
    D.dartVec d i
      = (if d = D.pos i then (1 : ℤ) else 0) - (if d = D.neg i then (1 : ℤ) else 0) := by
  rcases hsym : D.dart.symm d with c | c
  · have hd : d = D.pos c := by rw [pos, ← hsym, Equiv.apply_symm_apply]
    have hdv : D.dartVec d = Pi.single c (1 : ℤ) := by
      rw [dartVec, hsym]
      rfl
    subst hd
    rw [hdv, Pi.single_apply]
    by_cases hci : i = c
    · subst hci
      rw [if_pos rfl, if_pos rfl, if_neg (D.pos_ne_neg i i)]
      norm_num
    · rw [if_neg hci, if_neg (fun h => hci (D.pos_injective h).symm),
        if_neg (D.pos_ne_neg c i)]
      norm_num
  · have hd : d = D.neg c := by rw [neg, ← hsym, Equiv.apply_symm_apply]
    have hdv : D.dartVec d = Pi.single c (-1 : ℤ) := by
      rw [dartVec, hsym]
      rfl
    subst hd
    rw [hdv, Pi.single_apply]
    by_cases hci : i = c
    · subst hci
      rw [if_pos rfl, if_neg (D.pos_ne_neg i i).symm, if_pos rfl]
      norm_num
    · rw [if_neg hci, if_neg ((D.pos_ne_neg i c).symm),
        if_neg (fun h => hci (D.neg_injective h).symm)]
      norm_num

p2m_export "PDPairing.Chord.ChordDiagram" "dartVec_apply_eq"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceVecAt_apply_eq (p : Fin (2 * n)) (i : Fin n) :
    D.faceVecAt p i
      = (if D.pos i ∈ D.orbitFinset p then (1 : ℤ) else 0)
        - (if D.neg i ∈ D.orbitFinset p then (1 : ℤ) else 0) := by
  rw [faceVecAt_eq_orbit_sum]
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun d _ => D.dartVec_apply_eq d i]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

p2m_export "PDPairing.Chord.ChordDiagram" "faceVecAt_apply_eq"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceFamily : Finset (Fin n → ℤ) :=
  Finset.univ.image D.faceVecAt

p2m_export "PDPairing.Chord.ChordDiagram" "faceFamily"
private theorem _root_.PDPairing.Chord.ChordDiagram.colProp_faceFamily : PDPairing.Sat.ColProp D.faceFamily := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf i
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hf
    rw [faceVecAt_apply_eq]
    split_ifs <;> norm_num
  · intro i f hf g hg hfi hgi
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hg
    have hp : D.pos i ∈ D.orbitFinset p := by
      by_contra hcon
      rw [faceVecAt_apply_eq, if_neg hcon] at hfi
      split_ifs at hfi <;> omega
    have hp' : D.pos i ∈ D.orbitFinset p' := by
      by_contra hcon
      rw [faceVecAt_apply_eq, if_neg hcon] at hgi
      split_ifs at hgi <;> omega
    rw [← D.faceVecAt_eq_of_mem hp, ← D.faceVecAt_eq_of_mem hp']
  · intro i f hf g hg hfi hgi
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hg
    have hp : D.neg i ∈ D.orbitFinset p := by
      by_contra hcon
      rw [faceVecAt_apply_eq, if_neg hcon] at hfi
      split_ifs at hfi <;> omega
    have hp' : D.neg i ∈ D.orbitFinset p' := by
      by_contra hcon
      rw [faceVecAt_apply_eq, if_neg hcon] at hgi
      split_ifs at hgi <;> omega
    rw [← D.faceVecAt_eq_of_mem hp, ← D.faceVecAt_eq_of_mem hp']

p2m_export "PDPairing.Chord.ChordDiagram" "colProp_faceFamily"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceLattice_saturated_direct (v : Fin n → ℤ) (k : ℤ) (hk : k ≠ 0)
    (h : k • v ∈ D.faceLattice) : v ∈ D.faceLattice := by
  have hspan : D.faceLattice
      = Submodule.span ℤ ((D.faceFamily : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := by
    rw [faceLattice, faceFamily]
    congr 1
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hspan] at h ⊢
  exact PDPairing.Sat.span_saturated_of_colProp _ D.colProp_faceFamily v k hk h

p2m_export "PDPairing.Chord.ChordDiagram" "faceLattice_saturated_direct"
private theorem _root_.PDPairing.Chord.ChordDiagram.eps_cases (i j : Fin n) : D.eps i j = -1 ∨ D.eps i j = 0 ∨ D.eps i j = 1 := by
  unfold eps
  split_ifs <;> simp

p2m_export "PDPairing.Chord.ChordDiagram" "eps_cases"
@[scoped simp]
private theorem _root_.PDPairing.Chord.ChordDiagram.epsFormQ_mk (v w : Fin n → ℤ) :
    D.epsFormQ (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) = D.epsForm v w := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "epsFormQ_mk"
private theorem _root_.PDPairing.Chord.ChordDiagram.epsForm_skew (u v : Fin n → ℤ) : D.epsForm u v = -D.epsForm v u := by
  rw [eq_neg_iff_add_eq_zero]
  have h : D.epsForm u v + D.epsForm v u
      = ∑ i, ∑ j, (u i * D.eps i j * v j + v j * D.eps j i * u i) := by
    show (∑ i, ∑ j, u i * D.eps i j * v j) + (∑ i, ∑ j, v i * D.eps i j * u j) = _
    rw [show (∑ i, ∑ j, v i * D.eps i j * u j) = ∑ i, ∑ j, v j * D.eps j i * u i from
      Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
  rw [h]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [D.eps_skew j i]
  ring

p2m_export "PDPairing.Chord.ChordDiagram" "epsForm_skew"
private def _root_.PDPairing.Chord.ChordDiagram.entryDart (j : Fin n) (s : Bool) : Fin (2 * n) := if s then D.neg j else D.pos j

p2m_export "PDPairing.Chord.ChordDiagram" "entryDart"
private def _root_.PDPairing.Chord.ChordDiagram.exitDart (j : Fin n) (s : Bool) : Fin (2 * n) := if s then D.pos j else D.neg j

p2m_export "PDPairing.Chord.ChordDiagram" "exitDart"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitIdx_exists (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) :
    ∃ t, (D.facePerm ^ t) x = y :=
  (Finset.mem_image.mp hy).imp fun _ hk => hk.2

p2m_export "PDPairing.Chord.ChordDiagram" "orbitIdx_exists"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.orbitIdx (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) : ℕ :=
  Nat.find (D.orbitIdx_exists x y hy)

p2m_export "PDPairing.Chord.ChordDiagram" "orbitIdx"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitIdx_spec (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) :
    (D.facePerm ^ D.orbitIdx x y hy) x = y :=
  Nat.find_spec (D.orbitIdx_exists x y hy)

p2m_export "PDPairing.Chord.ChordDiagram" "orbitIdx_spec"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitIdx_le (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) (t : ℕ)
    (ht : (D.facePerm ^ t) x = y) : D.orbitIdx x y hy ≤ t :=
  Nat.find_min' (D.orbitIdx_exists x y hy) ht

p2m_export "PDPairing.Chord.ChordDiagram" "orbitIdx_le"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.segSum (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) : Fin n → ℤ :=
  ∑ l ∈ Finset.range (D.orbitIdx x y hy), D.dartVec ((D.facePerm ^ l) x)

p2m_export "PDPairing.Chord.ChordDiagram" "segSum"
private structure _root_.PDPairing.Chord.ChordDiagram.DualCycle (D' : ChordDiagram n) where
  m : ℕ
  hm : 0 < m
  chord : ℕ → Fin n
  sgn : ℕ → Bool
  chord_per : ∀ k, chord (k + m) = chord k
  sgn_per : ∀ k, sgn (k + m) = sgn k
  compat : ∀ k, D'.entryDart (chord (k + 1)) (sgn (k + 1))
      ∈ D'.orbitFinset (D'.facePerm (D'.exitDart (chord k) (sgn k)))

p2m_export "PDPairing.Chord.ChordDiagram" "DualCycle"
p2m_export_all "PDPairing.Chord.ChordDiagram" "DualCycle"
private def _root_.PDPairing.Chord.ChordDiagram.cycInd (C : DualCycle D) : Fin n → ℤ := fun j =>
  ∑ k ∈ Finset.range C.m, (if C.chord k = j then (if C.sgn k then (1 : ℤ) else -1) else 0)

p2m_export "PDPairing.Chord.ChordDiagram" "cycInd"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.cycReal (C : DualCycle D) : Fin n → ℤ :=
  ∑ k ∈ Finset.range C.m,
    D.segSum (D.facePerm (D.exitDart (C.chord k) (C.sgn k)))
      (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (C.compat k)

p2m_export "PDPairing.Chord.ChordDiagram" "cycReal"
private theorem _root_.PDPairing.Chord.ChordDiagram.orbitFinset_eq_of_mem {p d : Fin (2 * n)} (hd : d ∈ D.orbitFinset p) :
    D.orbitFinset d = D.orbitFinset p := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hd
  exact D.orbitFinset_pow_apply p k

p2m_export "PDPairing.Chord.ChordDiagram" "orbitFinset_eq_of_mem"
private theorem _root_.PDPairing.Chord.ChordDiagram.mem_orbitFinset_iff (x p : Fin (2 * n)) :
    x ∈ D.orbitFinset p ↔ D.orbitFinset x = D.orbitFinset p :=
  ⟨D.orbitFinset_eq_of_mem, fun h => h ▸ D.mem_orbitFinset_self x⟩

p2m_export "PDPairing.Chord.ChordDiagram" "mem_orbitFinset_iff"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_entryDart (j : Fin n) (s : Bool) :
    D.partner (D.entryDart j s) = D.exitDart j s := by
  unfold entryDart exitDart
  cases s <;> simp [partner_pos, partner_neg]

p2m_export "PDPairing.Chord.ChordDiagram" "partner_entryDart"
private theorem _root_.PDPairing.Chord.ChordDiagram.partner_exitDart (j : Fin n) (s : Bool) :
    D.partner (D.exitDart j s) = D.entryDart j s := by
  rw [← D.partner_entryDart, partner_partner]

p2m_export "PDPairing.Chord.ChordDiagram" "partner_exitDart"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_range_shift (f : ℕ → ℤ) (m : ℕ) (hf : f m = f 0) :
    (∑ k ∈ Finset.range m, f (k + 1)) = ∑ k ∈ Finset.range m, f k := by
  have hs1 := Finset.sum_range_succ' f m
  have hs2 := Finset.sum_range_succ f m
  omega

p2m_export "PDPairing.Chord.ChordDiagram" "sum_range_shift"
private theorem _root_.PDPairing.Chord.ChordDiagram.segSum_pairing (x y : Fin (2 * n)) (hy : y ∈ D.orbitFinset x) (j : Fin n) :
    (2 * (n : ℤ)) * (∑ i, D.segSum x y hy i * D.eps i j)
      = (((cdist y (D.pos j) : ℤ) - cdist y (D.neg j))
        - ((cdist x (D.pos j) : ℤ) - cdist x (D.neg j))) := by
  classical
  set t := D.orbitIdx x y hy with ht

  have hcol : (∑ i, D.segSum x y hy i * D.eps i j)
      = ∑ l ∈ Finset.range t,
          ((if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.pos j)
              then (1 : ℤ) else 0)
            - (if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.neg j)
              then (1 : ℤ) else 0)) := by
    unfold segSum
    rw [show (∑ i, (∑ l ∈ Finset.range t, D.dartVec ((D.facePerm ^ l) x)) i * D.eps i j)
        = ∑ l ∈ Finset.range t, (∑ i, D.dartVec ((D.facePerm ^ l) x) i * D.eps i j) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_apply, Finset.sum_mul]]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [D.dart_collapse]

  have htel : (2 * (n : ℤ)) * (∑ l ∈ Finset.range t,
      ((if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.pos j)
          then (1 : ℤ) else 0)
        - (if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.neg j)
          then (1 : ℤ) else 0)))
      = (((cdist ((D.facePerm ^ t) x) (D.pos j) : ℤ) - cdist ((D.facePerm ^ t) x) (D.neg j))
        - ((cdist x (D.pos j) : ℤ) - cdist x (D.neg j))) := by
    rw [Finset.mul_sum]
    set g : ℕ → ℤ := fun l =>
      (cdist ((D.facePerm ^ l) x) (D.pos j) : ℤ) - cdist ((D.facePerm ^ l) x) (D.neg j) with hg
    have hstep : ∀ l, (2 * (n : ℤ)) *
        ((if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.pos j)
            then (1 : ℤ) else 0)
          - (if ArcMem ((D.facePerm ^ l) x) (D.partner ((D.facePerm ^ l) x)) (D.neg j)
            then (1 : ℤ) else 0)) = g (l + 1) - g l := by
      intro l
      have h := D.step_diff ((D.facePerm ^ l) x) (D.pos j)
      rw [D.partner_pos] at h
      have hsucc : (D.facePerm ^ (l + 1)) x = D.facePerm ((D.facePerm ^ l) x) := by
        rw [pow_succ']
        rfl
      rw [hg]
      simp only [hsucc]
      exact h
    rw [Finset.sum_congr rfl fun l _ => hstep l]
    exact Finset.sum_range_sub g t
  rw [hcol, htel, ht, D.orbitIdx_spec x y hy]

p2m_export "PDPairing.Chord.ChordDiagram" "segSum_pairing"
private theorem _root_.PDPairing.Chord.ChordDiagram.cycInd_orth (C : DualCycle D) (p : Fin (2 * n)) :
    (∑ i, D.faceVecAt p i * cycInd D C i) = 0 := by
  classical

  have h1 : (∑ i, D.faceVecAt p i * cycInd D C i)
      = ∑ k ∈ Finset.range C.m,
          (if C.sgn k then (1 : ℤ) else -1) * D.faceVecAt p (C.chord k) := by
    unfold cycInd
    have hpush : (∑ i, D.faceVecAt p i * ∑ k ∈ Finset.range C.m,
        (if C.chord k = i then (if C.sgn k then (1 : ℤ) else -1) else 0))
        = ∑ i, ∑ k ∈ Finset.range C.m,
          (if C.chord k = i then D.faceVecAt p i * (if C.sgn k then (1 : ℤ) else -1) else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [hpush, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp [mul_comm]

  have h2 : ∀ k, (if C.sgn k then (1 : ℤ) else -1) * D.faceVecAt p (C.chord k)
      = (if D.exitDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0)
        - (if D.entryDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0) := by
    intro k
    rw [faceVecAt_apply_eq]
    unfold entryDart exitDart
    cases C.sgn k <;> simp

  have hGF : ∀ k,
      (if D.entryDart (C.chord (k + 1)) (C.sgn (k + 1)) ∈ D.orbitFinset p then (1 : ℤ) else 0)
      = (if D.exitDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0) := by
    intro k
    have hc := C.compat k
    rw [D.orbitFinset_apply] at hc
    have hiff : D.entryDart (C.chord (k + 1)) (C.sgn (k + 1)) ∈ D.orbitFinset p
        ↔ D.exitDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p := by
      rw [D.mem_orbitFinset_iff, D.mem_orbitFinset_iff (D.exitDart (C.chord k) (C.sgn k)),
        D.orbitFinset_eq_of_mem hc]
    rw [if_congr hiff rfl rfl]

  have hshift : ∀ f : ℕ → ℤ, f C.m = f 0 →
      (∑ k ∈ Finset.range C.m, f (k + 1)) = ∑ k ∈ Finset.range C.m, f k := by
    intro f hf
    have hs1 := Finset.sum_range_succ' f C.m
    have hs2 := Finset.sum_range_succ f C.m
    omega

  rw [h1, Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_sub_distrib]
  have hper : (fun k => (if D.entryDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p
      then (1 : ℤ) else 0)) C.m
      = (fun k => (if D.entryDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0))
        0 := by
    simp only []
    rw [show C.m = 0 + C.m from (Nat.zero_add C.m).symm, C.chord_per, C.sgn_per]
  have hswap : (∑ k ∈ Finset.range C.m,
      (if D.entryDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0))
      = ∑ k ∈ Finset.range C.m,
        (if D.exitDart (C.chord k) (C.sgn k) ∈ D.orbitFinset p then (1 : ℤ) else 0) := by
    rw [← hshift _ hper]
    exact Finset.sum_congr rfl fun k _ => hGF k
  rw [hswap, sub_self]

p2m_export "PDPairing.Chord.ChordDiagram" "cycInd_orth"
private theorem _root_.PDPairing.Chord.ChordDiagram.cycReal_eq (C : DualCycle D) (j : Fin n) :
    (∑ i, cycReal D C i * D.eps i j) = cycInd D C j := by
  classical
  have h2n : 0 < 2 * n := (D.pos j).pos
  have h2nz : (2 * (n : ℤ)) ≠ 0 := by
    have : (0 : ℤ) < 2 * n := by exact_mod_cast h2n
    omega
  apply mul_left_cancel₀ h2nz
  have hexch : (∑ i, cycReal D C i * D.eps i j)
      = ∑ k ∈ Finset.range C.m, ∑ i,
          D.segSum (D.facePerm (D.exitDart (C.chord k) (C.sgn k)))
            (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (C.compat k) i * D.eps i j := by
    unfold cycReal
    rw [show (∑ i, (∑ k ∈ Finset.range C.m,
          D.segSum (D.facePerm (D.exitDart (C.chord k) (C.sgn k)))
            (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (C.compat k)) i * D.eps i j)
        = ∑ i, ∑ k ∈ Finset.range C.m,
            D.segSum (D.facePerm (D.exitDart (C.chord k) (C.sgn k)))
              (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (C.compat k) i * D.eps i j from
      Finset.sum_congr rfl fun i _ => by rw [Finset.sum_apply, Finset.sum_mul]]
    exact Finset.sum_comm
  rw [hexch, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.range C.m) =>
    D.segSum_pairing (D.facePerm (D.exitDart (C.chord k) (C.sgn k)))
      (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (C.compat k) j]
  have hstart : ∀ k, D.facePerm (D.exitDart (C.chord k) (C.sgn k))
      = (finRotate (2 * n)) (D.entryDart (C.chord k) (C.sgn k)) := fun k => by
    rw [D.facePerm_apply, D.partner_exitDart]
  simp only [hstart]
  rw [Finset.sum_sub_distrib]
  have hper : ((cdist (D.entryDart (C.chord C.m) (C.sgn C.m)) (D.pos j) : ℤ)
        - cdist (D.entryDart (C.chord C.m) (C.sgn C.m)) (D.neg j))
      = ((cdist (D.entryDart (C.chord 0) (C.sgn 0)) (D.pos j) : ℤ)
        - cdist (D.entryDart (C.chord 0) (C.sgn 0)) (D.neg j)) := by
    rw [show C.m = 0 + C.m from (Nat.zero_add _).symm, C.chord_per, C.sgn_per]
  rw [show (∑ k ∈ Finset.range C.m,
        ((cdist (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (D.pos j) : ℤ)
          - cdist (D.entryDart (C.chord (k + 1)) (C.sgn (k + 1))) (D.neg j)))
      = ∑ k ∈ Finset.range C.m,
        ((cdist (D.entryDart (C.chord k) (C.sgn k)) (D.pos j) : ℤ)
          - cdist (D.entryDart (C.chord k) (C.sgn k)) (D.neg j)) from
    sum_range_shift (fun l => (cdist (D.entryDart (C.chord l) (C.sgn l)) (D.pos j) : ℤ)
      - cdist (D.entryDart (C.chord l) (C.sgn l)) (D.neg j)) C.m hper]
  rw [← Finset.sum_sub_distrib]
  have hrot : ∀ k,
      (((cdist (D.entryDart (C.chord k) (C.sgn k)) (D.pos j) : ℤ)
          - cdist (D.entryDart (C.chord k) (C.sgn k)) (D.neg j))
        - ((cdist ((finRotate (2 * n)) (D.entryDart (C.chord k) (C.sgn k))) (D.pos j) : ℤ)
          - cdist ((finRotate (2 * n)) (D.entryDart (C.chord k) (C.sgn k))) (D.neg j)))
      = (2 * (n : ℤ)) * ((if D.neg j = D.entryDart (C.chord k) (C.sgn k) then (1 : ℤ) else 0)
          - (if D.pos j = D.entryDart (C.chord k) (C.sgn k) then (1 : ℤ) else 0)) := by
    intro k
    have h := D.rotate_phi (D.entryDart (C.chord k) (C.sgn k)) (D.pos j)
    rw [D.partner_pos] at h
    linarith
  rw [Finset.sum_congr rfl fun k _ => hrot k, ← Finset.mul_sum]
  congr 1
  unfold cycInd
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold entryDart
  have hnp : ∀ (a b : Fin n), D.neg a ≠ D.pos b := fun a b h => D.pos_ne_neg b a h.symm
  by_cases hcj : C.chord k = j
  · subst hcj
    cases hsk : C.sgn k <;> simp [D.pos_ne_neg, hnp]
  · have hpp : D.pos j ≠ D.pos (C.chord k) := fun h => hcj (D.pos_injective h.symm)
    have hnn : D.neg j ≠ D.neg (C.chord k) := fun h => hcj (D.neg_injective h.symm)
    cases hsk : C.sgn k <;> simp [D.pos_ne_neg, hnp, hpp, hnn, hcj]

p2m_export "PDPairing.Chord.ChordDiagram" "cycReal_eq"
private def _root_.PDPairing.Chord.ChordDiagram.flowSgn (w : Fin n → ℤ) (j : Fin n) : Bool := decide (0 < w j)

p2m_export "PDPairing.Chord.ChordDiagram" "flowSgn"
private theorem _root_.PDPairing.Chord.ChordDiagram.flowSgn_true {w : Fin n → ℤ} {j : Fin n} (h : 0 < w j) : flowSgn w j = true :=
  decide_eq_true h

p2m_export "PDPairing.Chord.ChordDiagram" "flowSgn_true"
private theorem _root_.PDPairing.Chord.ChordDiagram.flowSgn_false {w : Fin n → ℤ} {j : Fin n} (h : w j < 0) : flowSgn w j = false := by
  unfold flowSgn
  rw [decide_eq_false_iff_not]
  omega

p2m_export "PDPairing.Chord.ChordDiagram" "flowSgn_false"
private theorem _root_.PDPairing.Chord.ChordDiagram.exists_dualCycle_of_loop (w : Fin n → ℤ) (j : Fin n) (hj : w j ≠ 0)
    (hloop : D.neg j ∈ D.orbitFinset (D.pos j)) :
    ∃ C : DualCycle D, (∀ i, cycInd D C i ≠ 0 → 0 < w i * cycInd D C i) ∧
      (∀ i, |cycInd D C i| ≤ 1) ∧ (∃ i, cycInd D C i ≠ 0) := by
  classical
  have horb : D.orbitFinset (D.neg j) = D.orbitFinset (D.pos j) :=
    D.orbitFinset_eq_of_mem hloop
  have hcompat : ∀ s : Bool, D.entryDart j s ∈ D.orbitFinset (D.facePerm (D.exitDart j s)) := by
    intro s
    rw [D.orbitFinset_apply]
    cases s
    · show D.pos j ∈ D.orbitFinset (D.neg j)
      rw [horb]
      exact D.mem_orbitFinset_self _
    · show D.neg j ∈ D.orbitFinset (D.pos j)
      exact hloop
  refine ⟨⟨1, one_pos, fun _ => j, fun _ => flowSgn w j, fun _ => rfl, fun _ => rfl,
    fun _ => hcompat _⟩, ?_, ?_, ?_⟩
  · intro i hi
    unfold cycInd at hi ⊢
    rw [Finset.sum_range_one] at hi ⊢
    by_cases hij : j = i
    · subst hij
      rw [if_pos rfl] at hi ⊢
      rcases lt_or_gt_of_ne hj with h | h
      · rw [flowSgn_false h]
        simp only [Bool.false_eq_true, if_false]
        nlinarith
      · rw [flowSgn_true h]
        simp only [if_true]
        nlinarith
    · rw [if_neg hij] at hi
      exact absurd rfl hi
  · intro i
    unfold cycInd
    rw [Finset.sum_range_one]
    split_ifs <;> norm_num
  · refine ⟨j, ?_⟩
    unfold cycInd
    rw [Finset.sum_range_one, if_pos rfl]
    cases flowSgn w j <;> norm_num

p2m_export "PDPairing.Chord.ChordDiagram" "exists_dualCycle_of_loop"
private theorem _root_.PDPairing.Chord.ChordDiagram.exists_continuation (w : Fin n → ℤ)
    (hw : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0)
    (hnoloop : ∀ i, w i ≠ 0 → D.neg i ∉ D.orbitFinset (D.pos i))
    (j : Fin n) (hj : w j ≠ 0) :
    ∃ j', w j' ≠ 0 ∧ D.entryDart j' (flowSgn w j')
      ∈ D.orbitFinset (D.facePerm (D.exitDart j (flowSgn w j))) := by
  classical
  by_contra hcon
  push Not at hcon
  set p := D.exitDart j (flowSgn w j) with hp
  have hnot : ∀ j', w j' ≠ 0 → D.entryDart j' (flowSgn w j') ∉ D.orbitFinset p := by
    intro j' hj' hmem
    exact (hcon j' hj') (by rwa [D.orbitFinset_apply])
  have hterm : ∀ i, 0 ≤ ((if D.pos i ∈ D.orbitFinset p then (1 : ℤ) else 0)
      - (if D.neg i ∈ D.orbitFinset p then (1 : ℤ) else 0)) * w i := by
    intro i
    by_cases hi : w i = 0
    · rw [hi, mul_zero]
    · rcases lt_or_gt_of_ne hi with h | h
      · have hent : D.pos i ∉ D.orbitFinset p := by
          have := hnot i hi
          rwa [show D.entryDart i (flowSgn w i) = D.pos i from by
            rw [flowSgn_false h]; rfl] at this
        rw [if_neg hent]
        split_ifs <;> nlinarith
      · have hent : D.neg i ∉ D.orbitFinset p := by
          have := hnot i hi
          rwa [show D.entryDart i (flowSgn w i) = D.neg i from by
            rw [flowSgn_true h]; rfl] at this
        rw [if_neg hent]
        split_ifs <;> nlinarith
  have hstrict : 0 < ((if D.pos j ∈ D.orbitFinset p then (1 : ℤ) else 0)
      - (if D.neg j ∈ D.orbitFinset p then (1 : ℤ) else 0)) * w j := by
    rcases lt_or_gt_of_ne hj with h | h
    · have hpdef : p = D.neg j := by rw [hp, flowSgn_false h]; rfl
      have h1 : D.neg j ∈ D.orbitFinset p := hpdef ▸ D.mem_orbitFinset_self _
      have h2 : D.pos j ∉ D.orbitFinset p := by
        rw [hpdef]
        intro hmem
        have heq : D.orbitFinset (D.pos j) = D.orbitFinset (D.neg j) :=
          D.orbitFinset_eq_of_mem hmem
        refine hnoloop j hj ?_
        rw [heq]
        exact D.mem_orbitFinset_self _
      rw [if_neg h2, if_pos h1]
      nlinarith
    · have hpdef : p = D.pos j := by rw [hp, flowSgn_true h]; rfl
      have h1 : D.pos j ∈ D.orbitFinset p := hpdef ▸ D.mem_orbitFinset_self _
      have h2 : D.neg j ∉ D.orbitFinset p := by
        rw [hpdef]
        exact hnoloop j hj
      rw [if_pos h1, if_neg h2]
      nlinarith
  have hsum0 : (∑ i, ((if D.pos i ∈ D.orbitFinset p then (1 : ℤ) else 0)
      - (if D.neg i ∈ D.orbitFinset p then (1 : ℤ) else 0)) * w i) = 0 := by
    have := hw p
    rw [Finset.sum_congr rfl fun i _ => by rw [D.faceVecAt_apply_eq]] at this
    exact this
  have hpos : 0 < (∑ i, ((if D.pos i ∈ D.orbitFinset p then (1 : ℤ) else 0)
      - (if D.neg i ∈ D.orbitFinset p then (1 : ℤ) else 0)) * w i) :=
    Finset.sum_pos' (fun i _ => hterm i) ⟨j, Finset.mem_univ j, hstrict⟩
  omega

p2m_export "PDPairing.Chord.ChordDiagram" "exists_continuation"
private theorem _root_.PDPairing.Chord.ChordDiagram.cycInd_mk {m : ℕ} {hm : 0 < m} {chord : ℕ → Fin n} {sgn : ℕ → Bool}
    {hc : ∀ k, chord (k + m) = chord k} {hs : ∀ k, sgn (k + m) = sgn k}
    {hcp : ∀ k, D.entryDart (chord (k + 1)) (sgn (k + 1))
      ∈ D.orbitFinset (D.facePerm (D.exitDart (chord k) (sgn k)))} {i : Fin n} :
    cycInd D ⟨m, hm, chord, sgn, hc, hs, hcp⟩ i
      = ∑ k ∈ Finset.range m, (if chord k = i then (if sgn k then (1 : ℤ) else -1) else 0) :=
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "cycInd_mk"
private theorem _root_.PDPairing.Chord.ChordDiagram.exists_dualCycle (w : Fin n → ℤ)
    (hw : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0) (hne : w ≠ 0) :
    ∃ C : DualCycle D, (∀ j, cycInd D C j ≠ 0 → 0 < w j * cycInd D C j) ∧
      (∀ j, |cycInd D C j| ≤ 1) ∧ (∃ j, cycInd D C j ≠ 0) := by
  classical
  by_cases hloopE : ∃ i, w i ≠ 0 ∧ D.neg i ∈ D.orbitFinset (D.pos i)
  · obtain ⟨i, hi, hl⟩ := hloopE
    exact D.exists_dualCycle_of_loop w i hi hl
  · push Not at hloopE
    obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    choose nxt hnxt1 hnxt2 using fun j hj => D.exists_continuation w hw hloopE j hj
    set W : ℕ → {j : Fin n // w j ≠ 0} :=
      fun k => Nat.rec (⟨j₀, hj₀⟩ : {j : Fin n // w j ≠ 0})
        (fun _ prev => ⟨nxt prev.1 prev.2, hnxt1 prev.1 prev.2⟩) k with hWdef
    have hWsucc : ∀ k, W (k + 1) = ⟨nxt (W k).1 (W k).2, hnxt1 (W k).1 (W k).2⟩ :=
      fun _ => rfl
    set c : ℕ → Fin n := fun k => (W k).1 with hc
    have hcne : ∀ k, w (c k) ≠ 0 := fun k => (W k).2
    have hWstep : ∀ k, D.entryDart (c (k + 1)) (flowSgn w (c (k + 1)))
        ∈ D.orbitFinset (D.facePerm (D.exitDart (c k) (flowSgn w (c k)))) := by
      intro k
      have h := hnxt2 (W k).1 (W k).2
      have hck : c (k + 1) = nxt (W k).1 (W k).2 := rfl
      rw [hck]
      exact h
    obtain ⟨a, b, hab, heqab⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (n + 1) => c k.val)
      (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
    have hex : ∃ b₀, ∃ a₀, a₀ < b₀ ∧ c a₀ = c b₀ := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨b.val, a.val, h, heqab⟩
      · exact ⟨a.val, b.val, h, heqab.symm⟩
    set b₀ := Nat.find hex with hb₀
    obtain ⟨a₀, ha₀lt, ha₀eq⟩ := Nat.find_spec hex
    set m := b₀ - a₀ with hm
    have hmpos : 0 < m := by omega
    have hwin : ∀ x y, a₀ ≤ x → x < y → y < b₀ → c x ≠ c y := by
      intro x y _ hxy hyb heq
      exact Nat.find_min hex hyb ⟨x, hxy, heq⟩
    have hshape : ∀ i, (∑ k ∈ Finset.range m,
        (if c (a₀ + k % m) = i then (if flowSgn w (c (a₀ + k % m)) then (1 : ℤ) else -1) else 0))
        = ∑ k ∈ Finset.range m,
          (if c (a₀ + k) = i then (if flowSgn w (c (a₀ + k)) then (1 : ℤ) else -1) else 0) := by
      refine fun i => Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
    have hcompat : ∀ k, D.entryDart (c (a₀ + (k + 1) % m)) (flowSgn w (c (a₀ + (k + 1) % m)))
        ∈ D.orbitFinset (D.facePerm (D.exitDart (c (a₀ + k % m))
            (flowSgn w (c (a₀ + k % m))))) := by
      intro k
      have hklt : k % m < m := Nat.mod_lt k hmpos
      have hmodsucc : (k + 1) % m = (k % m + 1) % m := by
        conv_lhs => rw [show k + 1 = k % m + 1 + m * (k / m) from by
          have := Nat.div_add_mod k m
          omega]
        rw [Nat.add_mul_mod_self_left]
      by_cases hk : k % m + 1 < m
      · have h1 : (k + 1) % m = k % m + 1 := by rw [hmodsucc, Nat.mod_eq_of_lt hk]
        rw [h1, show a₀ + (k % m + 1) = (a₀ + k % m) + 1 from by omega]
        exact hWstep (a₀ + k % m)
      · have hkm : k % m + 1 = m := by omega
        have h1 : (k + 1) % m = 0 := by rw [hmodsucc, hkm, Nat.mod_self]
        rw [h1, Nat.add_zero]
        have h4 := hWstep (a₀ + k % m)
        rw [show a₀ + k % m + 1 = b₀ from by omega, ← ha₀eq] at h4
        exact h4
    refine ⟨⟨m, hmpos, fun k => c (a₀ + k % m), fun k => flowSgn w (c (a₀ + k % m)),
      fun k => by
        show c (a₀ + (k + m) % m) = c (a₀ + k % m)
        rw [Nat.add_mod_right],
      fun k => by
        show flowSgn w (c (a₀ + (k + m) % m)) = flowSgn w (c (a₀ + k % m))
        rw [Nat.add_mod_right],
      hcompat⟩, ?_, ?_, ?_⟩
    ·
      intro i hi
      rw [D.cycInd_mk, hshape i] at hi ⊢
      by_cases hhit : ∃ k₀, k₀ ∈ Finset.range m ∧ c (a₀ + k₀) = i
      · obtain ⟨k₀, hk₀m, hk₀e⟩ := hhit
        have hsingle : (∑ k ∈ Finset.range m,
            (if c (a₀ + k) = i then (if flowSgn w (c (a₀ + k)) then (1 : ℤ) else -1) else 0))
            = (if c (a₀ + k₀) = i then (if flowSgn w (c (a₀ + k₀)) then (1 : ℤ) else -1)
              else 0) := by
          refine Finset.sum_eq_single_of_mem k₀ hk₀m fun k hk hkne => if_neg fun he => ?_
          have hcc : c (a₀ + k) = c (a₀ + k₀) := he.trans hk₀e.symm
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · exact hwin (a₀ + k) (a₀ + k₀) (by omega) (by omega)
              (by have := Finset.mem_range.mp hk₀m; omega) hcc
          · exact hwin (a₀ + k₀) (a₀ + k) (by omega) (by omega)
              (by have := Finset.mem_range.mp hk; omega) hcc.symm
        rw [hsingle, if_pos hk₀e] at hi ⊢
        have hwi : w i ≠ 0 := hk₀e ▸ hcne (a₀ + k₀)
        rcases lt_or_gt_of_ne hwi with hneg | hpos
        · rw [hk₀e, flowSgn_false hneg]
          simp only [Bool.false_eq_true, if_false]
          nlinarith
        · rw [hk₀e, flowSgn_true hpos]
          simp only [if_true]
          nlinarith
      · exfalso
        exact hi (Finset.sum_eq_zero fun k hk => if_neg fun he => hhit ⟨k, hk, he⟩)
    ·
      intro i
      rw [D.cycInd_mk, hshape i]
      by_cases hhit : ∃ k₀, k₀ ∈ Finset.range m ∧ c (a₀ + k₀) = i
      · obtain ⟨k₀, hk₀m, hk₀e⟩ := hhit
        have hsingle : (∑ k ∈ Finset.range m,
            (if c (a₀ + k) = i then (if flowSgn w (c (a₀ + k)) then (1 : ℤ) else -1) else 0))
            = (if c (a₀ + k₀) = i then (if flowSgn w (c (a₀ + k₀)) then (1 : ℤ) else -1)
              else 0) := by
          refine Finset.sum_eq_single_of_mem k₀ hk₀m fun k hk hkne => if_neg fun he => ?_
          have hcc : c (a₀ + k) = c (a₀ + k₀) := he.trans hk₀e.symm
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · exact hwin (a₀ + k) (a₀ + k₀) (by omega) (by omega)
              (by have := Finset.mem_range.mp hk₀m; omega) hcc
          · exact hwin (a₀ + k₀) (a₀ + k) (by omega) (by omega)
              (by have := Finset.mem_range.mp hk; omega) hcc.symm
        rw [hsingle]
        split_ifs <;> norm_num
      · rw [Finset.sum_eq_zero fun k hk => if_neg fun he => hhit ⟨k, hk, he⟩]
        norm_num
    ·
      refine ⟨c a₀, ?_⟩
      rw [D.cycInd_mk, hshape (c a₀)]
      have hsingle : (∑ k ∈ Finset.range m,
          (if c (a₀ + k) = c a₀ then (if flowSgn w (c (a₀ + k)) then (1 : ℤ) else -1) else 0))
          = (if c (a₀ + 0) = c a₀ then (if flowSgn w (c (a₀ + 0)) then (1 : ℤ) else -1)
            else 0) := by
        refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hmpos)
          fun k hk hkne => if_neg fun he => ?_
        have hcc : c (a₀ + 0) = c (a₀ + k) := by
          rw [he]
          norm_num
        exact hwin (a₀ + 0) (a₀ + k) (by omega) (by omega)
          (by have := Finset.mem_range.mp hk; omega) hcc
      rw [hsingle, if_pos (by norm_num)]
      cases flowSgn w (c (a₀ + 0)) <;> norm_num

p2m_export "PDPairing.Chord.ChordDiagram" "exists_dualCycle"
private theorem _root_.PDPairing.Chord.ChordDiagram.exists_epsForm_eq (w : Fin n → ℤ)
    (hw : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0) :
    ∃ v : Fin n → ℤ, ∀ j, (∑ i, v i * D.eps i j) = w j := by
  classical
  have H : ∀ N : ℕ, ∀ w : Fin n → ℤ,
      (∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0) → (∑ j, |w j|).toNat = N →
      ∃ v : Fin n → ℤ, ∀ j, (∑ i, v i * D.eps i j) = w j := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro w hw hN
      by_cases hne : w = 0
      · refine ⟨fun _ => 0, fun j => ?_⟩
        rw [hne]
        simp
      · obtain ⟨C, hsf, hunit, ⟨j₁, hj₁⟩⟩ := D.exists_dualCycle w hw hne
        set w' : Fin n → ℤ := fun j => w j - cycInd D C j with hw'
        have hw'div : ∀ p, (∑ i, D.faceVecAt p i * w' i) = 0 := by
          intro p
          rw [show (∑ i, D.faceVecAt p i * w' i)
              = (∑ i, D.faceVecAt p i * w i) - (∑ i, D.faceVecAt p i * cycInd D C i) from by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hw']
            ring]
          rw [hw p, D.cycInd_orth C p, sub_zero]
        have habs : ∀ j, cycInd D C j ≠ 0 → |w j - cycInd D C j| < |w j| := by
          intro j hz
          have hsf' := hsf j hz
          have hu := hunit j
          rcases abs_le.mp hu with ⟨hl, hr⟩
          rcases lt_trichotomy (cycInd D C j) 0 with h | h | h
          · have hind : cycInd D C j = -1 := by omega
            rw [hind] at hsf' ⊢
            rw [mul_neg_one] at hsf'
            have hwj : w j < 0 := by omega
            rw [show w j - -1 = w j + 1 from by ring, abs_of_nonpos (by omega),
              abs_of_neg hwj]
            omega
          · exact absurd h hz
          · have hind : cycInd D C j = 1 := by omega
            rw [hind] at hsf' ⊢
            rw [mul_one] at hsf'
            have hwj : 0 < w j := hsf'
            rw [abs_of_nonneg (by omega), abs_of_pos hwj]
            omega
        have hle : ∀ j, |w' j| ≤ |w j| := by
          intro j
          by_cases hz : cycInd D C j = 0
          · simp only [hw', hz, sub_zero]
            exact le_refl _
          · exact le_of_lt (habs j hz)
        have hstrict : |w' j₁| < |w j₁| := habs j₁ hj₁
        have hdrop : (∑ j, |w' j|) < ∑ j, |w j| := by
          calc (∑ j, |w' j|) = |w' j₁| + ∑ j ∈ Finset.univ.erase j₁, |w' j| := by
                rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ j₁)]
            _ < |w j₁| + ∑ j ∈ Finset.univ.erase j₁, |w j| :=
                add_lt_add_of_lt_of_le hstrict (Finset.sum_le_sum fun j _ => hle j)
            _ = ∑ j, |w j| := by rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ j₁)]
        have hN' : (∑ j, |w' j|).toNat < N := by
          have h0 : (0 : ℤ) ≤ ∑ j, |w' j| := Finset.sum_nonneg fun j _ => abs_nonneg _
          have h0' : (0 : ℤ) ≤ ∑ j, |w j| := Finset.sum_nonneg fun j _ => abs_nonneg _
          omega
        obtain ⟨v', hv'⟩ := ih _ hN' w' hw'div rfl
        refine ⟨fun i => v' i + cycReal D C i, fun j => ?_⟩
        rw [show (∑ i, (v' i + cycReal D C i) * D.eps i j)
            = (∑ i, v' i * D.eps i j) + (∑ i, cycReal D C i * D.eps i j) from by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring]
        rw [hv' j, D.cycReal_eq C j]
        simp only [hw']
        ring
  exact H _ w hw rfl

p2m_export "PDPairing.Chord.ChordDiagram" "exists_epsForm_eq"
private theorem _root_.PDPairing.Chord.ChordDiagram.ker_le_faceLattice (v : Fin n → ℤ) (hv : D.epsForm v = 0) : v ∈ D.faceLattice := by
  classical
  by_contra hcon
  haveI : Module.IsTorsionFree ℤ D.ParQuot := by
    refine ⟨fun r hr => ?_⟩
    have hrne : r ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hr.left (show (0 : ℤ) * 1 = 0 * 0 by ring))
    intro q₁ q₂ hq
    simp only [] at hq
    obtain ⟨u₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨u₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    have hq2 : D.faceLattice.mkQ (r • u₁) = D.faceLattice.mkQ (r • u₂) := by
      rw [map_smul, map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
      exact hq
    have hq' : D.faceLattice.mkQ (r • (u₁ - u₂)) = 0 := by
      calc D.faceLattice.mkQ (r • (u₁ - u₂))
          = D.faceLattice.mkQ (r • u₁) - D.faceLattice.mkQ (r • u₂) := by
            rw [← map_sub]
            congr 1
            rw [smul_sub]
        _ = 0 := by rw [hq2, sub_self]
    have hmem : r • (u₁ - u₂) ∈ D.faceLattice := by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.Quotient.eq]
    exact D.faceLattice_saturated_direct _ r hrne hmem
  haveI : Module.Finite ℤ D.ParQuot :=
    Module.Finite.of_surjective D.faceLattice.mkQ (Submodule.mkQ_surjective _)
  have hmkv : Submodule.Quotient.mk (p := D.faceLattice) v ≠ 0 := fun h =>
    hcon ((Submodule.Quotient.mk_eq_zero _).mp h)
  obtain ⟨φ, hφ⟩ : ∃ φ : D.ParQuot →ₗ[ℤ] ℤ, φ (Submodule.Quotient.mk v) ≠ 0 := by
    set b := Module.Free.chooseBasis ℤ D.ParQuot with hb
    have hrepr : b.repr (Submodule.Quotient.mk v) ≠ 0 := fun h =>
      hmkv (b.repr.injective (by rw [h, map_zero]))
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
    refine ⟨b.coord i, ?_⟩
    rw [Module.Basis.coord_apply]
    simpa using hi
  set w : Fin n → ℤ := fun j => φ (Submodule.Quotient.mk (Pi.single j 1)) with hwdef
  have hrep : ∀ u : Fin n → ℤ, φ (Submodule.Quotient.mk u) = ∑ j, u j * w j := by
    intro u
    have h1 : u = ∑ j, u j • Pi.single j (1 : ℤ) := by
      ext i
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    have hu : (Submodule.Quotient.mk u : D.ParQuot)
        = ∑ j, u j • (Submodule.Quotient.mk (Pi.single j (1 : ℤ)) : D.ParQuot) := by
      conv_lhs => rw [h1]
      rw [← Submodule.mkQ_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Submodule.mkQ_apply]
    rw [hu, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hworth : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0 := by
    intro p
    have hmem : D.faceVecAt p ∈ D.faceLattice := Submodule.subset_span ⟨p, rfl⟩
    have hzero : Submodule.Quotient.mk (p := D.faceLattice) (D.faceVecAt p) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [← hrep, hzero, map_zero]
  obtain ⟨u, hu⟩ := D.exists_epsForm_eq w hworth
  apply hφ
  rw [hrep v]
  have h1 : (∑ j, v j * w j) = ∑ j, v j * (∑ i, u i * D.eps i j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j]
  have h2 : (∑ j, v j * (∑ i, u i * D.eps i j)) = D.epsForm u v := by
    show _ = (∑ i, ∑ j, u i * D.eps i j * v j)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, h2, D.epsForm_skew u v, hv, LinearMap.zero_apply, neg_zero]

p2m_export "PDPairing.Chord.ChordDiagram" "ker_le_faceLattice"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceLattice_saturated (v : Fin n → ℤ) (k : ℤ) (hk : k ≠ 0)
    (h : k • v ∈ D.faceLattice) : v ∈ D.faceLattice := by
  refine D.ker_le_faceLattice v ?_
  have hker : D.epsForm (k • v) = 0 := by
    have := D.faceLattice_le_ker h
    rwa [LinearMap.mem_ker] at this
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.zero_apply]
  have hkv : D.epsForm (k • v) w = k * D.epsForm v w := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h0 : k * D.epsForm v w = 0 := by rw [← hkv, hker, LinearMap.zero_apply]
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact absurd h' hk
  · exact h'

p2m_export "PDPairing.Chord.ChordDiagram" "faceLattice_saturated"
private theorem _root_.PDPairing.Chord.ChordDiagram.epsFormQ_perfect : Function.Bijective D.epsFormQ := by
  classical
  constructor
  ·
    intro q₁ q₂ hq
    obtain ⟨v₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨v₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    rw [Submodule.Quotient.eq]
    refine D.ker_le_faceLattice _ ?_
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    have h1 : D.epsForm (v₁ - v₂) w = D.epsForm v₁ w - D.epsForm v₂ w := by
      rw [map_sub, LinearMap.sub_apply]
    have h2 : D.epsForm v₁ w = D.epsForm v₂ w := by
      have h := congrArg (fun F => F (Submodule.Quotient.mk (p := D.faceLattice) w)) hq
      simpa using h
    rw [h1, h2, sub_self]
  ·
    intro φ
    set w : Fin n → ℤ := fun j => φ (Submodule.Quotient.mk (Pi.single j 1)) with hwdef
    have hrep : ∀ u : Fin n → ℤ, φ (Submodule.Quotient.mk u) = ∑ j, u j * w j := by
      intro u
      have h1 : u = ∑ j, u j • Pi.single j (1 : ℤ) := by
        ext i
        rw [Finset.sum_apply]
        simp [Pi.single_apply]
      have hu : (Submodule.Quotient.mk u : D.ParQuot)
          = ∑ j, u j • (Submodule.Quotient.mk (Pi.single j (1 : ℤ)) : D.ParQuot) := by
        conv_lhs => rw [h1]
        rw [← Submodule.mkQ_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Submodule.mkQ_apply]
      rw [hu, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    have hworth : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * w i) = 0 := by
      intro p
      have hmem : D.faceVecAt p ∈ D.faceLattice :=
        Submodule.subset_span ⟨p, rfl⟩
      have hzero : Submodule.Quotient.mk (p := D.faceLattice) (D.faceVecAt p) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hmem
      rw [← hrep, hzero, map_zero]
    obtain ⟨v, hv⟩ := D.exists_epsForm_eq w hworth
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    refine LinearMap.ext fun q => ?_
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [epsFormQ_mk, hrep u]
    show (∑ i, ∑ j, v i * D.eps i j * u j) = ∑ j, u j * w j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hv j]
    ring

p2m_export "PDPairing.Chord.ChordDiagram" "epsFormQ_perfect"
private def _root_.PDPairing.Chord.ChordDiagram.letterAt (v : Fin n → ℤ) (q : Fin (2 * n)) : ℤ := ∑ i, D.dartVec q i * v i

p2m_export "PDPairing.Chord.ChordDiagram" "letterAt"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAt_eps_row (k : Fin n) (q : Fin (2 * n)) :
    D.letterAt (fun j => D.eps k j) q
      = (if ArcMem q (D.partner q) (D.neg k) then (1 : ℤ) else 0)
        - (if ArcMem q (D.partner q) (D.pos k) then (1 : ℤ) else 0) := by
  unfold letterAt
  have h1 : (∑ i, D.dartVec q i * D.eps k i) = -(∑ i, D.dartVec q i * D.eps i k) := by
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [D.eps_skew i k]
    ring
  rw [show (∑ i, D.dartVec q i * (fun j => D.eps k j) i) = ∑ i, D.dartVec q i * D.eps k i from
    rfl, h1, D.dart_collapse]
  ring

p2m_export "PDPairing.Chord.ChordDiagram" "letterAt_eps_row"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAt_eps_row_step (k : Fin n) (q : Fin (2 * n)) :
    (2 * (n : ℤ)) * D.letterAt (fun j => D.eps k j) q
      = (((cdist (D.facePerm q) (D.neg k) : ℤ) - cdist (D.facePerm q) (D.pos k))
        - ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k))) := by
  rw [D.letterAt_eps_row]
  have h := D.step_diff q (D.neg k)
  rw [D.partner_neg] at h
  exact h

p2m_export "PDPairing.Chord.ChordDiagram" "letterAt_eps_row_step"
private theorem _root_.PDPairing.Chord.ChordDiagram.potential_gap (k j : Fin n) :
    (((cdist (D.pos j) (D.neg k) : ℤ) - cdist (D.pos j) (D.pos k))
      - ((cdist (D.neg j) (D.neg k) : ℤ) - cdist (D.neg j) (D.pos k)))
    = (2 * (n : ℤ)) * ((if j = k then (1 : ℤ) else 0) - D.eps k j) := by
  have hpn : D.pos j ≠ D.neg j := D.pos_ne_neg j j
  have h1 := arc_step (D.pos j) (D.neg j) (D.neg k) hpn
  have h2 := arc_step (D.pos j) (D.neg j) (D.pos k) hpn
  have hek : D.eps j k = (if ArcMem (D.pos j) (D.neg j) (D.pos k) then (1 : ℤ) else 0)
      - (if ArcMem (D.pos j) (D.neg j) (D.neg k) then (1 : ℤ) else 0) := rfl
  have hskew : D.eps k j = -D.eps j k := by rw [D.eps_skew j k]
  have hnk : (if D.neg k = D.pos j then (1 : ℤ) else 0) = 0 :=
    if_neg fun h => D.pos_ne_neg j k h.symm
  rw [hnk] at h1
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl] at h2
    rw [if_pos rfl, hskew, hek]
    have hna : ¬ArcMem (D.pos j) (D.neg j) (D.pos j) := fun h => by
      have := h.1
      rw [cdist_self] at this
      exact absurd this (lt_irrefl 0)
    have hnb : ¬ArcMem (D.pos j) (D.neg j) (D.neg j) := fun h => absurd h.2 (lt_irrefl _)
    rw [if_neg hna] at h2
    rw [if_neg hna, if_neg hnb] at hek ⊢
    split_ifs at h1 ⊢
    all_goals omega
  · have hpk : (if D.pos k = D.pos j then (1 : ℤ) else 0) = 0 :=
      if_neg fun h => hjk (D.pos_injective h.symm)
    rw [hpk] at h2
    rw [if_neg hjk, hskew, hek]
    split_ifs at h1 h2 ⊢ <;> omega

p2m_export "PDPairing.Chord.ChordDiagram" "potential_gap"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_mul_prefix (f g : ℕ → ℤ) (m : ℕ) :
    (∑ b ∈ Finset.range m, (f b * (∑ a ∈ Finset.range b, g a)
      + g b * (∑ a ∈ Finset.range b, f a) + f b * g b))
    = (∑ b ∈ Finset.range m, f b) * (∑ b ∈ Finset.range m, g b) := by
  induction m with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ f, Finset.sum_range_succ g]
    ring

p2m_export "PDPairing.Chord.ChordDiagram" "sum_mul_prefix"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.Hface (p : Fin (2 * n)) (α β : Fin n → ℤ) : ℤ :=
  -∑ a ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
    ∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      if a < b then
        D.letterAt α ((D.facePerm ^ a) p) * D.letterAt β ((D.facePerm ^ b) p)
          - D.letterAt β ((D.facePerm ^ a) p) * D.letterAt α ((D.facePerm ^ b) p)
      else 0

p2m_export "PDPairing.Chord.ChordDiagram" "Hface"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceReps : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun p => ∀ q ∈ D.orbitFinset p, p ≤ q

p2m_export "PDPairing.Chord.ChordDiagram" "faceReps"
@[scoped simp]
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAt_pos (v : Fin n → ℤ) (j : Fin n) : D.letterAt v (D.pos j) = v j := by
  unfold letterAt
  rw [Finset.sum_eq_single j]
  · rw [D.dartVec_apply_eq, if_pos rfl, if_neg (D.pos_ne_neg j j)]
    ring
  · intro i _ hij
    rw [D.dartVec_apply_eq, if_neg (fun h => hij (D.pos_injective h).symm),
      if_neg (D.pos_ne_neg j i)]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

p2m_export "PDPairing.Chord.ChordDiagram" "letterAt_pos"
@[scoped simp]
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAt_neg (v : Fin n → ℤ) (j : Fin n) : D.letterAt v (D.neg j) = -v j := by
  unfold letterAt
  rw [Finset.sum_eq_single j]
  · rw [D.dartVec_apply_eq, if_neg (fun h => D.pos_ne_neg j j h.symm), if_pos rfl]
    ring
  · intro i _ hij
    rw [D.dartVec_apply_eq, if_neg (fun h => D.pos_ne_neg i j h.symm),
      if_neg (fun h => hij (D.neg_injective h).symm)]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

p2m_export "PDPairing.Chord.ChordDiagram" "letterAt_neg"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_darts (g : Fin (2 * n) → ℤ) :
    (∑ q, g q) = ∑ j, (g (D.pos j) + g (D.neg j)) := by
  rw [← Equiv.sum_comp D.dart g, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "sum_darts"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_letter_orbit (v : Fin n → ℤ) (p : Fin (2 * n)) :
    (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      D.letterAt v ((D.facePerm ^ b) p)) = ∑ i, D.faceVecAt p i * v i := by
  have h1 : (∑ i, D.faceVecAt p i * v i) = ∑ q ∈ D.orbitFinset p, D.letterAt v q := by
    rw [show (∑ i, D.faceVecAt p i * v i)
        = ∑ i, ∑ q ∈ D.orbitFinset p, D.dartVec q i * v i from
      Finset.sum_congr rfl fun i _ => by
        rw [D.faceVecAt_eq_orbit_sum, Finset.sum_apply, Finset.sum_mul]]
    rw [Finset.sum_comm]
    rfl
  rw [h1]
  unfold orbitFinset
  rw [Finset.sum_image]
  intro a ha b hb hab
  have hab' : (D.facePerm ^ a) p = (D.facePerm ^ b) p := hab
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Set.mem_Iio.mpr (Finset.mem_range.mp ha)) (Set.mem_Iio.mpr (Finset.mem_range.mp hb))
    (by rwa [perm_pow_apply, perm_pow_apply] at hab')

p2m_export "PDPairing.Chord.ChordDiagram" "sum_letter_orbit"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_faceReps (g : Fin (2 * n) → ℤ) :
    (∑ p ∈ D.faceReps, ∑ q ∈ D.orbitFinset p, g q) = ∑ q, g q := by
  classical
  have hdisj : (↑D.faceReps : Set (Fin (2 * n))).PairwiseDisjoint
      (fun p => D.orbitFinset p) := by
    intro p₁ h₁ p₂ h₂ hne12
    refine Finset.disjoint_left.mpr fun q hq1 hq2 => hne12 ?_
    have e1 : D.orbitFinset q = D.orbitFinset p₁ := D.orbitFinset_eq_of_mem hq1
    have e2 : D.orbitFinset q = D.orbitFinset p₂ := D.orbitFinset_eq_of_mem hq2
    rw [Finset.mem_coe, faceReps, Finset.mem_filter] at h₁ h₂
    have hp12 : p₁ ≤ p₂ := h₁.2 p₂ (by
      rw [← e1, e2]
      exact D.mem_orbitFinset_self p₂)
    have hp21 : p₂ ≤ p₁ := h₂.2 p₁ (by
      rw [← e2, e1]
      exact D.mem_orbitFinset_self p₁)
    exact le_antisymm hp12 hp21
  have hcover : D.faceReps.biUnion (fun p => D.orbitFinset p) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun q => ?_
    rw [Finset.mem_biUnion]
    have hne : (D.orbitFinset q).Nonempty := ⟨q, D.mem_orbitFinset_self q⟩
    refine ⟨(D.orbitFinset q).min' hne, ?_, ?_⟩
    · rw [faceReps, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun r hr => ?_⟩
      rw [D.orbitFinset_eq_of_mem ((D.orbitFinset q).min'_mem hne)] at hr
      exact Finset.min'_le _ r hr
    · rw [D.orbitFinset_eq_of_mem ((D.orbitFinset q).min'_mem hne)]
      exact D.mem_orbitFinset_self q
  rw [← Finset.sum_biUnion hdisj, hcover]

p2m_export "PDPairing.Chord.ChordDiagram" "sum_faceReps"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_range_orbit (g : Fin (2 * n) → ℤ) (p : Fin (2 * n)) :
    (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p), g ((D.facePerm ^ b) p))
      = ∑ q ∈ D.orbitFinset p, g q := by
  unfold orbitFinset
  rw [Finset.sum_image]
  intro a ha b hb hab
  have hab' : (D.facePerm ^ a) p = (D.facePerm ^ b) p := hab
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Set.mem_Iio.mpr (Finset.mem_range.mp ha)) (Set.mem_Iio.mpr (Finset.mem_range.mp hb))
    (by rwa [perm_pow_apply, perm_pow_apply] at hab')

p2m_export "PDPairing.Chord.ChordDiagram" "sum_range_orbit"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_eps_row_letters (k : Fin n) (p : Fin (2 * n)) (b : ℕ) :
    (2 * (n : ℤ)) * (∑ a ∈ Finset.range b,
        D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p))
      = (((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ) - cdist ((D.facePerm ^ b) p) (D.pos k))
        - ((cdist p (D.neg k) : ℤ) - cdist p (D.pos k))) := by
  induction b with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, Equiv.Perm.one_apply,
      sub_self]
  | succ t ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := D.letterAt_eps_row_step k ((D.facePerm ^ t) p)
    have hsucc : D.facePerm ((D.facePerm ^ t) p) = (D.facePerm ^ (t + 1)) p := by
      rw [pow_succ']
      rfl
    rw [hsucc] at h
    rw [h]
    ring

p2m_export "PDPairing.Chord.ChordDiagram" "sum_eps_row_letters"
private theorem _root_.PDPairing.Chord.ChordDiagram.Hface_eq (p : Fin (2 * n)) (ψ : Fin n → ℤ) (k : Fin n)
    (hψf : (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      D.letterAt ψ ((D.facePerm ^ b) p)) = 0) :
    (2 * (n : ℤ)) * D.Hface p ψ (fun j => D.eps k j)
      = 2 * (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt ψ ((D.facePerm ^ b) p)
            * ((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
              - cdist ((D.facePerm ^ b) p) (D.pos k)))
        + (2 * (n : ℤ)) * (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt ψ ((D.facePerm ^ b) p)
            * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)) := by
  classical
  have hpref : ∀ (f : ℕ → ℤ), ∀ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      (∑ a ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p), if a < b then f a else 0)
        = ∑ a ∈ Finset.range b, f a := by
    intro f b hb
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    have := Finset.mem_range.mp hb
    omega
  have hHsplit : D.Hface p ψ (fun j => D.eps k j)
      = -(∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
            D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
              * (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p)))
        + (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
            D.letterAt ψ ((D.facePerm ^ b) p)
              * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p))) := by
    unfold Hface
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b hb => show
        (∑ a ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          if a < b then D.letterAt ψ ((D.facePerm ^ a) p)
              * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
            - D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)
              * D.letterAt ψ ((D.facePerm ^ b) p)
          else 0)
        = (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p))
            * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
          - (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p))
            * D.letterAt ψ ((D.facePerm ^ b) p) from by
      rw [← hpref (fun a => D.letterAt ψ ((D.facePerm ^ a) p)) b hb,
        ← hpref (fun a => D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)) b hb,
        Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun b _ => mul_comm
      (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p))
      (D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)),
      Finset.sum_congr rfl fun b _ => mul_comm
      (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p))
      (D.letterAt ψ ((D.facePerm ^ b) p))]
    ring
  have habel := sum_mul_prefix (fun b => D.letterAt ψ ((D.facePerm ^ b) p))
    (fun b => D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p))
    (Function.minimalPeriod (⇑D.facePerm) p)
  rw [hψf, zero_mul] at habel
  have habelR : (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      (D.letterAt ψ ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p))
        + D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p))
        + D.letterAt ψ ((D.facePerm ^ b) p)
          * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p))) = 0 := habel
  have habelS : (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        D.letterAt ψ ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
      + (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
            * (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p)))
      + (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt ψ ((D.facePerm ^ b) p)
            * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact habelR
  have habel2 : (2 * (n : ℤ)) * ((∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        D.letterAt ψ ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
      + (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p)
            * (∑ a ∈ Finset.range b, D.letterAt ψ ((D.facePerm ^ a) p)))
      + (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt ψ ((D.facePerm ^ b) p)
            * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p))) = 0 := by
    rw [habelS, mul_zero]
  have hkey : (2 * (n : ℤ)) * (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      D.letterAt ψ ((D.facePerm ^ b) p)
        * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
      = ∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          D.letterAt ψ ((D.facePerm ^ b) p)
            * ((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
              - cdist ((D.facePerm ^ b) p) (D.pos k)) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun b _ => show
        (2 * (n : ℤ)) * (D.letterAt ψ ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
        = D.letterAt ψ ((D.facePerm ^ b) p)
            * (((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
                - cdist ((D.facePerm ^ b) p) (D.pos k))
              - ((cdist p (D.neg k) : ℤ) - cdist p (D.pos k))) from by
      rw [show (2 * (n : ℤ)) * (D.letterAt ψ ((D.facePerm ^ b) p)
          * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
          = D.letterAt ψ ((D.facePerm ^ b) p) * ((2 * (n : ℤ))
            * (∑ a ∈ Finset.range b, D.letterAt (fun j => D.eps k j) ((D.facePerm ^ a) p)))
        from by ring, D.sum_eps_row_letters k p b]]
    rw [show (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        D.letterAt ψ ((D.facePerm ^ b) p)
          * (((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
              - cdist ((D.facePerm ^ b) p) (D.pos k))
            - ((cdist p (D.neg k) : ℤ) - cdist p (D.pos k))))
        = (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
            D.letterAt ψ ((D.facePerm ^ b) p)
              * ((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
                - cdist ((D.facePerm ^ b) p) (D.pos k)))
          - (∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
              D.letterAt ψ ((D.facePerm ^ b) p))
            * ((cdist p (D.neg k) : ℤ) - cdist p (D.pos k)) from by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring]
    rw [hψf, zero_mul, sub_zero]
  rw [hHsplit]
  linear_combination (-1 : ℤ) * habel2 + 2 * hkey

p2m_export "PDPairing.Chord.ChordDiagram" "Hface_eq"
private theorem _root_.PDPairing.Chord.ChordDiagram.evalComb (ψ : Fin n → ℤ)
    (hψ : ∀ p : Fin (2 * n), (∑ i, D.faceVecAt p i * ψ i) = 0) (k : Fin n) :
    (∑ p ∈ D.faceReps, D.Hface p ψ (fun j => D.eps k j)) = 2 * ψ k := by
  classical
  have h2n : 0 < 2 * n := (D.pos k).pos
  have h2nz : (2 * (n : ℤ)) ≠ 0 := by
    have : (0 : ℤ) < 2 * n := by exact_mod_cast h2n
    omega
  apply mul_left_cancel₀ h2nz
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p _ => D.Hface_eq p ψ k (by
    rw [D.sum_letter_orbit]
    exact hψ p)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ p ∈ D.faceReps, ∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        D.letterAt ψ ((D.facePerm ^ b) p)
          * ((cdist ((D.facePerm ^ b) p) (D.neg k) : ℤ)
            - cdist ((D.facePerm ^ b) p) (D.pos k)))
      = ∑ q, D.letterAt ψ q * ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k)) from by
    rw [← D.sum_faceReps (fun q => D.letterAt ψ q
      * ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k)))]
    exact Finset.sum_congr rfl fun p _ => D.sum_range_orbit
      (fun q => D.letterAt ψ q * ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k))) p]
  rw [show (∑ p ∈ D.faceReps, ∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        D.letterAt ψ ((D.facePerm ^ b) p)
          * D.letterAt (fun j => D.eps k j) ((D.facePerm ^ b) p))
      = ∑ q, D.letterAt ψ q * D.letterAt (fun j => D.eps k j) q from by
    rw [← D.sum_faceReps (fun q => D.letterAt ψ q * D.letterAt (fun j => D.eps k j) q)]
    exact Finset.sum_congr rfl fun p _ => D.sum_range_orbit
      (fun q => D.letterAt ψ q * D.letterAt (fun j => D.eps k j) q) p]
  have hS1 : (∑ q, D.letterAt ψ q * ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k)))
      = (2 * (n : ℤ)) * ψ k - (2 * (n : ℤ)) * (∑ j, D.eps k j * ψ j) := by
    rw [D.sum_darts (fun q => D.letterAt ψ q
      * ((cdist q (D.neg k) : ℤ) - cdist q (D.pos k)))]
    rw [Finset.sum_congr rfl fun j _ => show
        D.letterAt ψ (D.pos j) * ((cdist (D.pos j) (D.neg k) : ℤ) - cdist (D.pos j) (D.pos k))
          + D.letterAt ψ (D.neg j)
            * ((cdist (D.neg j) (D.neg k) : ℤ) - cdist (D.neg j) (D.pos k))
        = (2 * (n : ℤ)) * ((if j = k then (1 : ℤ) else 0) - D.eps k j) * ψ j from by
      rw [D.letterAt_pos, D.letterAt_neg, ← D.potential_gap k j]
      ring]
    rw [show (∑ j, (2 * (n : ℤ)) * ((if j = k then (1 : ℤ) else 0) - D.eps k j) * ψ j)
        = (2 * (n : ℤ)) * ((∑ j, if j = k then ψ j else 0) - ∑ j, D.eps k j * ψ j) from by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring]
    rw [Finset.sum_eq_single k (fun j _ hjk => if_neg hjk)
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
    ring
  have hS2 : (∑ q, D.letterAt ψ q * D.letterAt (fun j => D.eps k j) q)
      = 2 * (∑ j, D.eps k j * ψ j) := by
    rw [D.sum_darts (fun q => D.letterAt ψ q * D.letterAt (fun j => D.eps k j) q)]
    rw [Finset.sum_congr rfl fun j _ => show
        D.letterAt ψ (D.pos j) * D.letterAt (fun j' => D.eps k j') (D.pos j)
          + D.letterAt ψ (D.neg j) * D.letterAt (fun j' => D.eps k j') (D.neg j)
        = 2 * (D.eps k j * ψ j) from by
      rw [D.letterAt_pos, D.letterAt_neg, D.letterAt_pos, D.letterAt_neg]
      ring]
    rw [← Finset.mul_sum]
  rw [hS1, hS2]
  ring

p2m_export "PDPairing.Chord.ChordDiagram" "evalComb"
end ChordDiagram
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram"

end PDPairing.Chord
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing"

section prints
set_option pp.deepTerms true
set_option pp.proofs true
end prints
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord"

namespace PDPairing
namespace CDS4

open LinearMap Module

section Abstract

variable {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
variable {R : Type*} [CommRing R]
variable {P : Type*} [AddCommGroup P] [Module R P]

abbrev HomZR (L : Type*) [AddCommGroup L] (R : Type*) [CommRing R] : Type _ := L →ₗ[ℤ] R

noncomputable def intCastHomMap : (L →ₗ[ℤ] ℤ) →ₗ[ℤ] (HomZR L R) :=
  LinearMap.llcomp ℤ L ℤ R (Algebra.linearMap ℤ R)

omit [Module.Free ℤ L] [Module.Finite ℤ L] in
@[scoped simp] theorem intCastHomMap_apply (f : L →ₗ[ℤ] ℤ) (y : L) :
    (intCastHomMap f : HomZR L R) y = (f y : R) := rfl

noncomputable def epsR (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) : L →ₗ[ℤ] HomZR L R :=
  (intCastHomMap (R := R)).comp ε

omit [Module.Free ℤ L] [Module.Finite ℤ L] in
@[scoped simp] theorem epsR_apply (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (y z : L) :
    (epsR (R := R) ε y) z = (ε y z : R) := rfl

noncomputable def homCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L) :
    HomZR L R ≃ₗ[R] (ι → R) where
  toFun f := fun i => f (b i)
  map_add' f g := by ext i; rfl
  map_smul' r f := by ext i; simp
  invFun v := Finsupp.linearCombination ℤ (fun i => (v i : R)) ∘ₗ b.repr.toLinearMap
  left_inv f := by
    ext x
    show Finsupp.linearCombination ℤ (fun i => f (b i)) (b.repr x) = f x
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    conv_rhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
  right_inv v := by
    ext i
    show Finsupp.linearCombination ℤ (fun j => v j) (b.repr (b i)) = v i
    rw [b.repr_self, Finsupp.linearCombination_single, one_smul]

noncomputable def epsMatrix {ι : Type*} (b : Module.Basis ι ℤ L)
    (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) : Matrix ι ι ℤ := fun i j => ε (b i) (b j)

omit [Module.Free ℤ L] [Module.Finite ℤ L] in

theorem isUnit_det_epsMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hε : Function.Bijective ε) :
    IsUnit ((epsMatrix b ε).map (Int.castRingHom R)).det := by
  have hM : (epsMatrix b ε).transpose = LinearMap.toMatrix b b.dualBasis ε := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
    rfl
  have hdet : IsUnit (epsMatrix b ε).det := by
    rw [← Matrix.det_transpose, hM]
    exact LinearEquiv.isUnit_det (LinearEquiv.ofBijective ε hε) b b.dualBasis
  have := hdet.map (Int.castRingHom R)
  rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this

theorem dotProduct_perfect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : (ι → R) →ₗ[R] R) : ∃! v : ι → R, ∀ w : ι → R, (∑ i, v i * w i) = l w := by
  refine ⟨fun i => l (Pi.single i 1), fun w => ?_, fun v' hv' => ?_⟩
  · have hw : w = ∑ i, w i • Pi.single i (1 : R) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hw, map_sum]
    simp only [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext j
    have := hv' (Pi.single j 1)
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    exact this

noncomputable def epsROp {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L)
    (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hε : Function.Bijective ε) :
    (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofLinear
    (Matrix.toLin' ((epsMatrix b ε).map (Int.castRingHom R)).transpose)
    (Matrix.toLin' ((epsMatrix b ε).map (Int.castRingHom R)).transpose⁻¹)
    (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _
          (by rw [Matrix.det_transpose]; exact isUnit_det_epsMatrix_map b ε hε),
        Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _
          (by rw [Matrix.det_transpose]; exact isUnit_det_epsMatrix_map b ε hε),
        Matrix.toLin'_one])

omit [Module.Free ℤ L] [Module.Finite ℤ L] in
theorem epsROp_single {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L)
    (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hε : Function.Bijective ε) (j : ι) :
    epsROp (R := R) b ε hε (Pi.single j 1) = homCoord (R := R) b (epsR (R := R) ε (b j)) := by
  ext i
  show ((epsMatrix b ε).map (Int.castRingHom R)).transpose.mulVec (Pi.single j 1) i
    = (ε (b j)) (b i)
  rw [Matrix.mulVec_single_one]
  rfl

theorem perfect_of_eval
    (ε : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hε : Function.Bijective ε)
    (B : P →ₗ[R] P →ₗ[R] R) (hAlt : ∀ φ ψ, B φ ψ = - B ψ φ)
    (coord : P ≃ₗ[R] HomZR L R) [Invertible (2 : R)]
    (hEval : ∀ (ψ : P) (y : L), B ψ (coord.symm (epsR (R := R) ε y)) = (2 : R) • (coord ψ) y)
    (l : P →ₗ[R] R) :
    ∃! φ₀ : P, ∀ ψ : P, B φ₀ ψ = l ψ := by
  classical
  set b := Module.Free.chooseBasis ℤ L with hb
  set ι := Module.Free.ChooseBasisIndex ℤ L
  haveI : Fintype ι := inferInstance
  set π : P ≃ₗ[R] (ι → R) := coord.trans (homCoord (R := R) b) with hπ
  set Ξ := epsROp (R := R) b ε hε with hΞ

  have hKey : ∀ (ψ : P) (c : ι → R), B ψ (π.symm (Ξ c)) = (2 : R) • (∑ i, c i * (π ψ) i) := by
    intro ψ

    have hF : ∀ j : ι, B ψ (π.symm (Ξ (Pi.single j 1))) = (2 : R) • (π ψ) j := by
      intro j
      have h1 : π.symm (Ξ (Pi.single j 1)) = coord.symm (epsR (R := R) ε (b j)) := by
        rw [hΞ, epsROp_single, hπ]
        show coord.symm ((homCoord (R := R) b).symm (homCoord (R := R) b _)) = _
        rw [(homCoord (R := R) b).symm_apply_apply]
      rw [h1, hEval]; rfl
    intro c
    have hc : c = ∑ j, c j • Pi.single j (1 : R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hc, map_sum, map_sum, map_sum]
    simp only [map_smul, hF, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  set l' : (ι → R) →ₗ[R] R := (-⅟(2 : R)) • (l.comp π.symm.toLinearMap) with hl'
  obtain ⟨c₀, hc₀, huniq⟩ := dotProduct_perfect (R := R) l'
  refine ⟨π.symm (Ξ c₀), fun ψ => ?_, fun φ₁ hφ₁ => ?_⟩
  · rw [hAlt, hKey, hc₀, hl']
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [← mul_assoc, mul_neg, mul_invOf_self, neg_mul, one_mul, neg_neg]
  · have hφ₁' : ∀ w : ι → R, (∑ i, (Ξ.symm (π φ₁)) i * w i) = l' w := by
      intro w
      have hK := hKey (π.symm w) (Ξ.symm (π φ₁))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
        hAlt, hφ₁] at hK

      rw [hl']
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        smul_eq_mul]
      have h2 := congrArg ((⅟(2 : R)) * ·) hK.symm
      simp only [smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul, mul_neg] at h2
      rw [neg_mul]; exact h2
    have : Ξ.symm (π φ₁) = c₀ := huniq _ hφ₁'
    rw [← this, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end Abstract
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord"

end PDPairing.CDS4
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord"

namespace PDPairing
namespace CDS5

open PDPairing.Chord PDPairing.Chord.ChordDiagram PDPairing.CDS4

variable {n : ℕ} (D : ChordDiagram n)

scoped instance instFiniteParQuot : Module.Finite ℤ D.ParQuot :=
  Module.Finite.of_surjective D.faceLattice.mkQ (Submodule.mkQ_surjective _)

scoped instance instIsTorsionFreeParQuot : Module.IsTorsionFree ℤ D.ParQuot := by
  refine ⟨fun r hr => ?_⟩
  have hrne : r ≠ 0 := by
    rintro rfl
    exact one_ne_zero (hr.left (show (0 : ℤ) * 1 = 0 * 0 by ring))
  intro q₁ q₂ hq
  simp only [] at hq
  obtain ⟨u₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
  obtain ⟨u₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
  have hq2 : D.faceLattice.mkQ (r • u₁) = D.faceLattice.mkQ (r • u₂) := by
    rw [map_smul, map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact hq
  have hq' : D.faceLattice.mkQ (r • (u₁ - u₂)) = 0 := by
    calc D.faceLattice.mkQ (r • (u₁ - u₂))
        = D.faceLattice.mkQ (r • u₁) - D.faceLattice.mkQ (r • u₂) := by
          rw [← map_sub]
          congr 1
          rw [smul_sub]
      _ = 0 := by rw [hq2, sub_self]
  have hmem : r • (u₁ - u₂) ∈ D.faceLattice := by
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
  rw [Submodule.Quotient.eq]
  exact D.faceLattice_saturated_direct _ r hrne hmem

scoped instance instFreeParQuot : Module.Free ℤ D.ParQuot := Module.free_of_finite_type_torsion_free'

theorem perfect_of_eval_chord {R : Type*} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P]
    (B : P →ₗ[R] P →ₗ[R] R) (hAlt : ∀ φ ψ, B φ ψ = - B ψ φ)
    (coord : P ≃ₗ[R] HomZR D.ParQuot R) [Invertible (2 : R)]
    (hEval : ∀ (ψ : P) (y : D.ParQuot),
      B ψ (coord.symm (epsR (R := R) D.epsFormQ y)) = (2 : R) • (coord ψ) y)
    (l : P →ₗ[R] R) :
    ∃! φ₀ : P, ∀ ψ : P, B φ₀ ψ = l ψ :=
  perfect_of_eval D.epsFormQ D.epsFormQ_perfect B hAlt coord hEval l

end PDPairing.CDS5
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4"

namespace PDPairing
namespace CDS5b

open PDPairing.CDS4 PDPairing.Chord PDPairing.Chord.ChordDiagram

section Span

variable {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
variable (R : Type*) [CommRing R]

theorem span_range_intCastHomMap :
    Submodule.span R (Set.range (intCastHomMap (L := L) (R := R))) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun f _ => ?_
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  have hfe : f = ∑ j, f (b j) • intCastHomMap (L := L) (R := R) (b.coord j) := by
    apply b.ext
    intro i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, intCastHomMap_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Int.cast_ite,
      Int.cast_one, Int.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hfe]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨b.coord j, rfl⟩)

theorem ext_of_intCastHomMap {S : Type*} [AddCommGroup S] [Module R S]
    (l₁ l₂ : HomZR L R →ₗ[R] S)
    (h : ∀ f₀ : L →ₗ[ℤ] ℤ, l₁ (intCastHomMap f₀) = l₂ (intCastHomMap f₀)) :
    l₁ = l₂ :=
  LinearMap.ext_on_range (span_range_intCastHomMap (L := L) R) h

end Span
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section EvalQ

variable {n : ℕ} (D : ChordDiagram n)

noncomputable def vecCoord (f : D.ParQuot →ₗ[ℤ] ℤ) : Fin n → ℤ :=
  fun j => f (D.faceLattice.mkQ (Pi.single j 1))

theorem vecCoord_dot (f₀ : D.ParQuot →ₗ[ℤ] ℤ) (v : Fin n → ℤ) :
    (∑ i, v i * vecCoord D f₀ i) = f₀ (D.faceLattice.mkQ v) := by
  classical
  have hveq : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℤ) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_rhs => rw [hveq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, smul_eq_mul]
  rfl

theorem vecCoord_add (f g : D.ParQuot →ₗ[ℤ] ℤ) :
    vecCoord D (f + g) = vecCoord D f + vecCoord D g := rfl

theorem vecCoord_zsmul (c : ℤ) (f : D.ParQuot →ₗ[ℤ] ℤ) :
    vecCoord D (c • f) = c • vecCoord D f := rfl

theorem sum_faceVecAt_vecCoord (f₀ : D.ParQuot →ₗ[ℤ] ℤ) (p : Fin (2 * n)) :
    (∑ i, D.faceVecAt p i * vecCoord D f₀ i) = 0 := by
  rw [vecCoord_dot]
  have hmem : D.faceVecAt p ∈ D.faceLattice := Submodule.subset_span ⟨p, rfl⟩
  simp only [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]

theorem vecCoord_epsFormQ_mkQ_single (k j : Fin n) :
    vecCoord D (D.epsFormQ (D.faceLattice.mkQ (Pi.single k 1))) j = D.eps k j := by
  show D.epsFormQ (Submodule.Quotient.mk (Pi.single k 1)) (Submodule.Quotient.mk (Pi.single j 1))
    = D.eps k j
  rw [D.epsFormQ_mk]
  show (∑ a, ∑ b, (Pi.single k 1 : Fin n → ℤ) a * D.eps a b * (Pi.single j 1 : Fin n → ℤ) b)
    = D.eps k j
  classical
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem letterAt_add (v w : Fin n → ℤ) (q : Fin (2 * n)) :
    D.letterAt (v + w) q = D.letterAt v q + D.letterAt w q := by
  simp only [letterAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem letterAt_zsmul (c : ℤ) (v : Fin n → ℤ) (q : Fin (2 * n)) :
    D.letterAt (c • v) q = c * D.letterAt v q := by
  simp only [letterAt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Hface_add_right (p : Fin (2 * n)) (α β₁ β₂ : Fin n → ℤ) :
    D.Hface p α (β₁ + β₂) = D.Hface p α β₁ + D.Hface p α β₂ := by
  simp only [Hface, letterAt_add]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · ring
  · ring

theorem Hface_zsmul_right (p : Fin (2 * n)) (α β : Fin n → ℤ) (c : ℤ) :
    D.Hface p α (c • β) = c * D.Hface p α β := by
  simp only [Hface, letterAt_zsmul]
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · ring
  · ring

noncomputable def evalQLHS (f₀ : D.ParQuot →ₗ[ℤ] ℤ) : D.ParQuot →ₗ[ℤ] ℤ where
  toFun y := ∑ p ∈ D.faceReps, D.Hface p (vecCoord D f₀) (vecCoord D (D.epsFormQ y))
  map_add' y y' := by
    simp only [map_add, vecCoord_add, Hface_add_right, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [map_zsmul, vecCoord_zsmul, Hface_zsmul_right, Finset.mul_sum, smul_eq_mul,
      eq_intCast, Int.cast_id]

theorem evalQLHS_apply (f₀ : D.ParQuot →ₗ[ℤ] ℤ) (y : D.ParQuot) :
    evalQLHS D f₀ y
      = ∑ p ∈ D.faceReps, D.Hface p (vecCoord D f₀) (vecCoord D (D.epsFormQ y)) := rfl

theorem evalQ (f₀ : D.ParQuot →ₗ[ℤ] ℤ) (y : D.ParQuot) :
    (∑ p ∈ D.faceReps, D.Hface p (vecCoord D f₀) (vecCoord D (D.epsFormQ y)))
      = 2 * f₀ y := by
  classical
  have hL : (evalQLHS D f₀).comp D.faceLattice.mkQ
      = ((2 : ℤ) • f₀).comp D.faceLattice.mkQ := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro k
    simp only [LinearMap.comp_apply, evalQLHS_apply, LinearMap.smul_apply, smul_eq_mul,
      Pi.basisFun_apply]
    refine (Finset.sum_congr rfl fun p _ => ?_).trans
      (D.evalComb (vecCoord D f₀) (sum_faceVecAt_vecCoord D f₀) k)
    exact congrArg (D.Hface p (vecCoord D f₀))
      (funext fun j => vecCoord_epsFormQ_mkQ_single D k j)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have := LinearMap.congr_fun hL v
  simpa only [LinearMap.comp_apply, evalQLHS_apply, LinearMap.smul_apply, smul_eq_mul,
    Submodule.mkQ_apply] using this

end EvalQ
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

end PDPairing.CDS5b
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

namespace PDPairing
namespace Chord

open PDPairing.CDS4 PDPairing.CDS5 PDPairing.CDS5b Function Equiv
open scoped BigOperators

namespace ChordDiagram

variable {n : ℕ} (D : ChordDiagram n)

private theorem _root_.PDPairing.Chord.ChordDiagram.pos_or_neg (d : Fin (2 * n)) : (∃ i, d = D.pos i) ∨ (∃ i, d = D.neg i) := by
  rcases h : D.dart.symm d with i | i
  · exact Or.inl ⟨i, by rw [pos, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨i, by rw [neg, ← h, Equiv.apply_symm_apply]⟩

p2m_export "PDPairing.Chord.ChordDiagram" "pos_or_neg"
section GenM
variable {M : Type*} [AddCommMonoid M]

private theorem _root_.PDPairing.Chord.ChordDiagram.sum_darts_gen (g : Fin (2 * n) → M) :
    (∑ q, g q) = ∑ j, (g (D.pos j) + g (D.neg j)) := by
  rw [← Equiv.sum_comp D.dart g, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "sum_darts_gen"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_faceReps_gen (g : Fin (2 * n) → M) :
    (∑ p ∈ D.faceReps, ∑ q ∈ D.orbitFinset p, g q) = ∑ q, g q := by
  classical
  have hdisj : (↑D.faceReps : Set (Fin (2 * n))).PairwiseDisjoint
      (fun p => D.orbitFinset p) := by
    intro p₁ h₁ p₂ h₂ hne12
    refine Finset.disjoint_left.mpr fun q hq1 hq2 => hne12 ?_
    have e1 : D.orbitFinset q = D.orbitFinset p₁ := D.orbitFinset_eq_of_mem hq1
    have e2 : D.orbitFinset q = D.orbitFinset p₂ := D.orbitFinset_eq_of_mem hq2
    rw [Finset.mem_coe, faceReps, Finset.mem_filter] at h₁ h₂
    have hp12 : p₁ ≤ p₂ := h₁.2 p₂ (by rw [← e1, e2]; exact D.mem_orbitFinset_self p₂)
    have hp21 : p₂ ≤ p₁ := h₂.2 p₁ (by rw [← e2, e1]; exact D.mem_orbitFinset_self p₁)
    exact le_antisymm hp12 hp21
  have hcover : D.faceReps.biUnion (fun p => D.orbitFinset p) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun q => ?_
    rw [Finset.mem_biUnion]
    have hne : (D.orbitFinset q).Nonempty := ⟨q, D.mem_orbitFinset_self q⟩
    refine ⟨(D.orbitFinset q).min' hne, ?_, ?_⟩
    · rw [faceReps, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun r hr => ?_⟩
      rw [D.orbitFinset_eq_of_mem ((D.orbitFinset q).min'_mem hne)] at hr
      exact Finset.min'_le _ r hr
    · rw [D.orbitFinset_eq_of_mem ((D.orbitFinset q).min'_mem hne)]
      exact D.mem_orbitFinset_self q
  rw [← Finset.sum_biUnion hdisj, hcover]

p2m_export "PDPairing.Chord.ChordDiagram" "sum_faceReps_gen"
private theorem _root_.PDPairing.Chord.ChordDiagram.sum_faceReps_period_gen (g : Fin (2 * n) → M) :
    (∑ p ∈ D.faceReps, ∑ k ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
      g ((D.facePerm ^ k) p)) = ∑ q, g q := by
  rw [← D.sum_faceReps_gen g]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold orbitFinset
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Set.mem_Iio.mpr (Finset.mem_range.mp ha)) (Set.mem_Iio.mpr (Finset.mem_range.mp hb))
    (by simpa [← perm_pow_apply] using hab)

p2m_export "PDPairing.Chord.ChordDiagram" "sum_faceReps_period_gen"
end GenM
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section LetterAtR
variable {R : Type*} [CommRing R]

private def _root_.PDPairing.Chord.ChordDiagram.letterAtR (G : Fin n → R) (q : Fin (2 * n)) : R := ∑ i, (D.dartVec q i : R) * G i

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_pos (G : Fin n → R) (j : Fin n) : D.letterAtR G (D.pos j) = G j := by
  unfold letterAtR
  simp only [dartVec, pos, Equiv.symm_apply_apply, Sum.elim_inl,
    Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_pos"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_neg (G : Fin n → R) (j : Fin n) : D.letterAtR G (D.neg j) = -G j := by
  unfold letterAtR
  simp only [dartVec, neg, Equiv.symm_apply_apply, Sum.elim_inr,
    Pi.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg hb]; ring)
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_neg"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_partner (G : Fin n → R) (d : Fin (2 * n)) :
    D.letterAtR G (D.partner d) = -D.letterAtR G d := by
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := D.pos_or_neg d
  · rw [D.partner_pos, D.letterAtR_neg, D.letterAtR_pos]
  · rw [D.partner_neg, D.letterAtR_pos, D.letterAtR_neg, neg_neg]

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_partner"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_cast (v : Fin n → ℤ) (q : Fin (2 * n)) :
    D.letterAtR (fun i => (v i : R)) q = (D.letterAt v q : R) := by
  unfold letterAtR letterAt
  push_cast
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_cast"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_add (G₁ G₂ : Fin n → R) (q : Fin (2 * n)) :
    D.letterAtR (G₁ + G₂) q = D.letterAtR G₁ q + D.letterAtR G₂ q := by
  unfold letterAtR
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_add"
private theorem _root_.PDPairing.Chord.ChordDiagram.letterAtR_smul (r : R) (G : Fin n → R) (q : Fin (2 * n)) :
    D.letterAtR (r • G) q = r * D.letterAtR G q := by
  unfold letterAtR
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

p2m_export "PDPairing.Chord.ChordDiagram" "letterAtR_smul"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceSumR (G : Fin n → R) (p : Fin (2 * n)) : R :=
  ∑ k ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p), D.letterAtR G ((D.facePerm ^ k) p)

p2m_export "PDPairing.Chord.ChordDiagram" "faceSumR"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceSumR_eq_dot (G : Fin n → R) (p : Fin (2 * n)) :
    D.faceSumR G p = ∑ i, (D.faceVecAt p i : R) * G i := by
  unfold faceSumR letterAtR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [faceVecAt, Finset.sum_apply]
  push_cast
  rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceSumR_eq_dot"
end LetterAtR
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section FaceKer
variable {R : Type*} [CommRing R]

private def _root_.PDPairing.Chord.ChordDiagram.faceKer : Submodule R (Fin n → R) where
  carrier := {G | ∀ p : Fin (2 * n), D.faceSumR G p = 0}
  add_mem' := by
    intro G₁ G₂ h₁ h₂ p
    rw [show (G₁ + G₂) = (fun i => G₁ i + G₂ i) from rfl, faceSumR_eq_dot]
    simp only [mul_add, Finset.sum_add_distrib, ← faceSumR_eq_dot, h₁ p, h₂ p, add_zero]
  zero_mem' := by
    intro p
    rw [faceSumR_eq_dot]
    simp
  smul_mem' := by
    intro r G hG p
    rw [show r • G = (fun i => r * G i) from rfl, faceSumR_eq_dot]
    simp only [show ∀ i, (D.faceVecAt p i : R) * (r * G i) = r * ((D.faceVecAt p i : R) * G i)
      from fun i => by ring, ← Finset.mul_sum, ← faceSumR_eq_dot, hG p, mul_zero]

p2m_export "PDPairing.Chord.ChordDiagram" "faceKer"
private theorem _root_.PDPairing.Chord.ChordDiagram.mem_faceKer_iff (G : Fin n → R) :
    G ∈ D.faceKer (R := R) ↔ ∀ p : Fin (2 * n), D.faceSumR G p = 0 := Iff.rfl

p2m_export "PDPairing.Chord.ChordDiagram" "mem_faceKer_iff"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.dotHomR : (Fin n → ℤ) →ₗ[ℤ] (Fin n → R) →ₗ[R] R :=
  LinearMap.mk₂' ℤ R (fun v G => ∑ i, (v i : R) * G i)
    (fun v₁ v₂ G => by simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib])
    (fun c v G => by
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_assoc, zsmul_eq_mul,
        Finset.mul_sum])
    (fun v G₁ G₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r v G => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring)

p2m_export "PDPairing.Chord.ChordDiagram" "dotHomR"
private theorem _root_.PDPairing.Chord.ChordDiagram.dotHomR_apply (v : Fin n → ℤ) (G : Fin n → R) :
    dotHomR (R := R) v G = ∑ i, (v i : R) * G i := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "dotHomR_apply"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceKerToHom (G : D.faceKer (R := R)) : HomZR D.ParQuot R :=
  (D.faceLattice.liftQ (LinearMap.flip (dotHomR (R := R)) (G : Fin n → R))
    (Submodule.span_le.mpr (by
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply, dotHomR_apply,
        ← faceSumR_eq_dot]
      exact G.2 p)))

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerToHom"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceKerToHom_mk (G : D.faceKer (R := R)) (v : Fin n → ℤ) :
    D.faceKerToHom G (Submodule.Quotient.mk v) = ∑ i, (v i : R) * (G : Fin n → R) i := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerToHom_mk"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.vecCoordR (f : HomZR D.ParQuot R) : Fin n → R :=
  fun j => f (D.faceLattice.mkQ (Pi.single j 1))

p2m_export "PDPairing.Chord.ChordDiagram" "vecCoordR"
private theorem _root_.PDPairing.Chord.ChordDiagram.vecCoordR_mem_faceKer (f : HomZR D.ParQuot R) :
    D.vecCoordR f ∈ D.faceKer (R := R) := by
  intro p
  rw [faceSumR_eq_dot]
  have key : (D.faceLattice.mkQ (D.faceVecAt p)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨p, rfl⟩)
  calc ∑ i, (D.faceVecAt p i : R) * D.vecCoordR f i
      = ∑ i, (D.faceVecAt p i) • f (D.faceLattice.mkQ (Pi.single i 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [zsmul_eq_mul]; rfl
    _ = f (D.faceLattice.mkQ (∑ i, (D.faceVecAt p i) • Pi.single i 1)) := by
        rw [map_sum, map_sum]; exact (Finset.sum_congr rfl fun i _ => by
          rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]).symm
    _ = f (D.faceLattice.mkQ (D.faceVecAt p)) := by
        congr 1
        show D.faceLattice.mkQ _ = D.faceLattice.mkQ _
        congr 1; ext i
        simp [Finset.sum_apply, Pi.single_apply]
    _ = 0 := by rw [key, map_zero]

p2m_export "PDPairing.Chord.ChordDiagram" "vecCoordR_mem_faceKer"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceKerEquiv : D.faceKer (R := R) ≃ₗ[R] HomZR D.ParQuot R where
  toFun G := D.faceKerToHom G
  map_add' G₁ G₂ := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [LinearMap.add_apply, faceKerToHom_mk, Submodule.coe_add, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' r G := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [RingHom.id_apply, LinearMap.smul_apply, faceKerToHom_mk, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  invFun f := ⟨D.vecCoordR f, D.vecCoordR_mem_faceKer f⟩
  left_inv G := by
    apply Subtype.ext
    ext j
    show D.faceKerToHom G (Submodule.Quotient.mk (Pi.single j 1)) = (G : Fin n → R) j
    rw [faceKerToHom_mk]
    simp [Pi.single_apply]
  right_inv f := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show D.faceKerToHom ⟨D.vecCoordR f, _⟩ (Submodule.Quotient.mk v) = f (Submodule.Quotient.mk v)
    rw [faceKerToHom_mk]
    calc ∑ i, (v i : R) * D.vecCoordR f i
        = ∑ i, v i • f (D.faceLattice.mkQ (Pi.single i 1)) :=
          Finset.sum_congr rfl fun i _ => by rw [zsmul_eq_mul]; rfl
      _ = f (D.faceLattice.mkQ (∑ i, v i • Pi.single i 1)) := by
          rw [map_sum, map_sum]
          exact (Finset.sum_congr rfl fun i _ => by
            rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]).symm
      _ = f (Submodule.Quotient.mk v) := by
          congr 1
          show D.faceLattice.mkQ _ = D.faceLattice.mkQ v
          congr 1; ext i; simp [Finset.sum_apply, Pi.single_apply]

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerEquiv"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceKerEquiv_apply_mk (G : D.faceKer (R := R)) (v : Fin n → ℤ) :
    D.faceKerEquiv G (Submodule.Quotient.mk v) = ∑ i, (v i : R) * (G : Fin n → R) i := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerEquiv_apply_mk"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceKerEquiv_symm_coe (f : HomZR D.ParQuot R) (j : Fin n) :
    (↑(D.faceKerEquiv.symm f) : Fin n → R) j = f (D.faceLattice.mkQ (Pi.single j 1)) := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerEquiv_symm_coe"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceKerEquiv_symm_intCast (f₀ : D.ParQuot →ₗ[ℤ] ℤ) (j : Fin n) :
    (↑((D.faceKerEquiv (R := R)).symm (intCastHomMap f₀)) : Fin n → R) j
      = (vecCoord D f₀ j : R) := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerEquiv_symm_intCast"
end FaceKer
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section HfaceR
variable {R : Type*} [CommRing R]

private noncomputable def _root_.PDPairing.Chord.ChordDiagram.HfaceR (p : Fin (2 * n)) (G G' : Fin n → R) : R :=
  -∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
    ∑ a ∈ Finset.range b,
      (D.letterAtR G ((D.facePerm ^ a) p) * D.letterAtR G' ((D.facePerm ^ b) p)
        - D.letterAtR G' ((D.facePerm ^ a) p) * D.letterAtR G ((D.facePerm ^ b) p))

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_eq_double_range (p : Fin (2 * n)) (G G' : Fin n → R) :
    D.HfaceR p G G'
      = -∑ a ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
        ∑ b ∈ Finset.range (Function.minimalPeriod (⇑D.facePerm) p),
          if a < b then
            D.letterAtR G ((D.facePerm ^ a) p) * D.letterAtR G' ((D.facePerm ^ b) p)
              - D.letterAtR G' ((D.facePerm ^ a) p) * D.letterAtR G ((D.facePerm ^ b) p)
          else 0 := by
  unfold HfaceR
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨lt_trans h (Finset.mem_range.mp hb), h⟩, And.right⟩

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_eq_double_range"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_map (p : Fin (2 * n)) (α β : Fin n → ℤ) :
    D.HfaceR (R := R) p (fun i => (α i : R)) (fun i => (β i : R)) = (D.Hface p α β : R) := by
  rw [HfaceR_eq_double_range, Hface]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · simp only [letterAtR_cast]
  · simp

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_map"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_skew (p : Fin (2 * n)) (G G' : Fin n → R) :
    D.HfaceR p G G' = -D.HfaceR p G' G := by
  unfold HfaceR
  rw [neg_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_skew"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_add_left (p : Fin (2 * n)) (G₁ G₂ G' : Fin n → R) :
    D.HfaceR p (G₁ + G₂) G' = D.HfaceR p G₁ G' + D.HfaceR p G₂ G' := by
  simp only [HfaceR, letterAtR_add, ← Finset.sum_add_distrib, ← neg_add]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_add_left"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_smul_left (p : Fin (2 * n)) (r : R) (G G' : Fin n → R) :
    D.HfaceR p (r • G) G' = r * D.HfaceR p G G' := by
  simp only [HfaceR, letterAtR_smul, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_smul_left"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_add_right (p : Fin (2 * n)) (G G'₁ G'₂ : Fin n → R) :
    D.HfaceR p G (G'₁ + G'₂) = D.HfaceR p G G'₁ + D.HfaceR p G G'₂ := by
  rw [D.HfaceR_skew p G, D.HfaceR_skew p G G'₁, D.HfaceR_skew p G G'₂, HfaceR_add_left, neg_add]

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_add_right"
private theorem _root_.PDPairing.Chord.ChordDiagram.HfaceR_smul_right (p : Fin (2 * n)) (r : R) (G G' : Fin n → R) :
    D.HfaceR p G (r • G') = r * D.HfaceR p G G' := by
  rw [D.HfaceR_skew p G, D.HfaceR_skew p G G', HfaceR_smul_left, mul_neg]

p2m_export "PDPairing.Chord.ChordDiagram" "HfaceR_smul_right"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceFormR (G G' : Fin n → R) : R := ∑ p ∈ D.faceReps, D.HfaceR p G G'

p2m_export "PDPairing.Chord.ChordDiagram" "faceFormR"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceFormR_skew (G G' : Fin n → R) : D.faceFormR G G' = -D.faceFormR G' G := by
  unfold faceFormR
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => D.HfaceR_skew p G G'

p2m_export "PDPairing.Chord.ChordDiagram" "faceFormR_skew"
private noncomputable def _root_.PDPairing.Chord.ChordDiagram.faceFormRBilin :
    (D.faceKer (R := R)) →ₗ[R] (D.faceKer (R := R)) →ₗ[R] R :=
  LinearMap.mk₂ R (fun G G' => D.faceFormR (G : Fin n → R) (G' : Fin n → R))
    (fun G₁ G₂ G' => by
      simp only [faceFormR, Submodule.coe_add, HfaceR_add_left, Finset.sum_add_distrib])
    (fun r G G' => by
      simp only [faceFormR, Submodule.coe_smul, HfaceR_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun G G'₁ G'₂ => by
      simp only [faceFormR, Submodule.coe_add, HfaceR_add_right, Finset.sum_add_distrib])
    (fun r G G' => by
      simp only [faceFormR, Submodule.coe_smul, HfaceR_smul_right, Finset.mul_sum, smul_eq_mul])

p2m_export "PDPairing.Chord.ChordDiagram" "faceFormRBilin"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceFormRBilin_apply (G G' : D.faceKer (R := R)) :
    D.faceFormRBilin G G' = D.faceFormR (G : Fin n → R) (G' : Fin n → R) := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceFormRBilin_apply"
end HfaceR
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section Perfect
variable {R : Type*} [CommRing R]

private theorem _root_.PDPairing.Chord.ChordDiagram.faceKerEquiv_symm_epsR (y : D.ParQuot) (j : Fin n) :
    (↑((D.faceKerEquiv (R := R)).symm (epsR (R := R) D.epsFormQ y)) : Fin n → R) j
      = (vecCoord D (D.epsFormQ y) j : R) := rfl

p2m_export "PDPairing.Chord.ChordDiagram" "faceKerEquiv_symm_epsR"
variable [Invertible (2 : R)]

omit [Invertible (2 : R)] in

private theorem _root_.PDPairing.Chord.ChordDiagram.hEval_R (G₀ : D.faceKer (R := R)) (y : D.ParQuot) :
    D.faceFormRBilin G₀ ((D.faceKerEquiv (R := R)).symm (epsR (R := R) D.epsFormQ y))
      = (2 : R) • (D.faceKerEquiv G₀ y) := by

  have hβ : (↑((D.faceKerEquiv (R := R)).symm (epsR (R := R) D.epsFormQ y)) : Fin n → R)
      = fun j => (vecCoord D (D.epsFormQ y) j : R) := funext (D.faceKerEquiv_symm_epsR y)

  let L₁ : HomZR D.ParQuot R →ₗ[R] R :=
    ((D.faceFormRBilin (R := R)).flip
        ((D.faceKerEquiv (R := R)).symm (epsR (R := R) D.epsFormQ y))).comp
      (D.faceKerEquiv (R := R)).symm.toLinearMap
  let L₂ : HomZR D.ParQuot R →ₗ[R] R :=
    { toFun := fun F => (2 : R) • F y
      map_add' := fun F₁ F₂ => by
        show (2 : R) • (F₁ y + F₂ y) = (2 : R) • F₁ y + (2 : R) • F₂ y
        rw [smul_add]
      map_smul' := fun r F => by
        show (2 : R) • (r • F y) = r • ((2 : R) • F y)
        rw [smul_comm] }
  have hL : L₁ = L₂ := by
    apply ext_of_intCastHomMap
    intro f₀

    show D.faceFormRBilin ((D.faceKerEquiv (R := R)).symm (intCastHomMap f₀))
        ((D.faceKerEquiv (R := R)).symm (epsR (R := R) D.epsFormQ y))
      = (2 : R) • ((intCastHomMap f₀ : HomZR D.ParQuot R) y)
    rw [faceFormRBilin_apply, hβ]
    have hα : (↑((D.faceKerEquiv (R := R)).symm (intCastHomMap f₀)) : Fin n → R)
        = fun j => (vecCoord D f₀ j : R) := funext (D.faceKerEquiv_symm_intCast f₀)
    rw [hα, faceFormR]
    simp only [HfaceR_map]
    rw [← Int.cast_sum, evalQ D f₀ y, intCastHomMap_apply]
    push_cast
    ring
  have := LinearMap.congr_fun hL (D.faceKerEquiv G₀)
  simp only [L₁, L₂, LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, LinearMap.coe_mk, AddHom.coe_mk] at this
  exact this

p2m_export "PDPairing.Chord.ChordDiagram" "hEval_R"
private theorem _root_.PDPairing.Chord.ChordDiagram.faceFormR_perfect (l : D.faceKer (R := R) →ₗ[R] R) :
    ∃! G₀ : D.faceKer (R := R), ∀ G : D.faceKer (R := R), D.faceFormRBilin G₀ G = l G :=
  perfect_of_eval_chord D D.faceFormRBilin
    (fun G G' => by rw [faceFormRBilin_apply, faceFormRBilin_apply, faceFormR_skew])
    (D.faceKerEquiv (R := R)) (D.hEval_R (R := R)) l

p2m_export "PDPairing.Chord.ChordDiagram" "faceFormR_perfect"
end Perfect
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

end ChordDiagram
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

end PDPairing.Chord
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

namespace PDPairing
namespace Cover

variable {D : Type*} [DecidableEq D]

structure Fatgraph (s : Finset D) where
  rot : Equiv.Perm ↥s
  prt : Equiv.Perm ↥s
  prt_invol : ∀ d, prt (prt d) = d
  prt_ne : ∀ d, prt d ≠ d

namespace Fatgraph

variable {s : Finset D} (G : Fatgraph s)

def facePerm : Equiv.Perm ↥s := G.rot * G.prt

def SameVertex (d e : ↥s) : Prop := Equiv.Perm.SameCycle G.rot d e

structure StepEdge where
  d₀ : ↥s
  hcross : ¬ G.SameVertex d₀ (G.prt d₀)

variable (e : StepEdge G)

def StepEdge.a : ↥s := e.d₀

def StepEdge.b : ↥s := G.prt e.d₀

def StepEdge.live : Finset D := (s.erase ↑(e.a)).erase ↑(G.prt e.d₀)

theorem StepEdge.mem_live (x : D) :
    x ∈ e.live G ↔ x ∈ s ∧ x ≠ ↑(e.a) ∧ x ≠ ↑(e.b G) := by
  unfold StepEdge.live StepEdge.a StepEdge.b
  rw [Finset.mem_erase, Finset.mem_erase]
  tauto

def stepRotFun (x : ↥s) : ↥s :=
  if G.rot x = e.a then (if G.rot (e.b G) = e.b G then G.rot e.a else G.rot (e.b G))
  else if G.rot x = e.b G then (if G.rot e.a = e.a then G.rot (e.b G) else G.rot e.a)
  else G.rot x

def stepRotInvFun (y : ↥s) : ↥s :=
  if G.rot.symm y = e.a then
    (if G.rot.symm (e.b G) = e.b G then G.rot.symm e.a else G.rot.symm (e.b G))
  else if G.rot.symm y = e.b G then
    (if G.rot.symm e.a = e.a then G.rot.symm (e.b G) else G.rot.symm e.a)
  else G.rot.symm y

omit [DecidableEq D] in

theorem StepEdge.a_ne_b : e.a ≠ e.b G := fun h =>
  G.prt_ne e.d₀ ((show e.d₀ = G.prt e.d₀ from h).symm)

omit [DecidableEq D] in

theorem StepEdge.rot_a_ne_b : G.rot e.a ≠ e.b G := fun h =>
  e.hcross ⟨1, by simp at h ⊢; exact h⟩

omit [DecidableEq D] in

theorem StepEdge.rot_b_ne_a : G.rot (e.b G) ≠ e.a := fun h =>
  e.hcross (Equiv.Perm.SameCycle.symm ⟨1, by simp at h ⊢; exact h⟩)

omit [DecidableEq D] in
theorem StepEdge.symm_a_ne_b : G.rot.symm e.a ≠ e.b G := fun h =>
  e.rot_b_ne_a G (by rw [← h, Equiv.apply_symm_apply])

omit [DecidableEq D] in
theorem StepEdge.symm_b_ne_a : G.rot.symm (e.b G) ≠ e.a := fun h =>
  e.rot_a_ne_b G (by rw [← h, Equiv.apply_symm_apply])

theorem stepRotFun_mem_live (x : ↥s) (hx : (↑x : D) ∈ e.live G) :
    (↑(G.stepRotFun e x) : D) ∈ e.live G := by
  obtain ⟨-, hxa, hxb⟩ := (e.mem_live G ↑x).mp hx
  have hxa' : x ≠ e.a := fun h => hxa (congrArg _ h)
  have hxb' : x ≠ e.b G := fun h => hxb (congrArg _ h)
  unfold stepRotFun
  by_cases h1 : G.rot x = e.a
  · rw [if_pos h1]
    by_cases h2 : G.rot (e.b G) = e.b G
    · rw [if_pos h2, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => hxa' (G.rot.injective (h1.trans (Subtype.ext hc).symm)),
        fun hc => e.rot_a_ne_b G (Subtype.ext hc)⟩
    · rw [if_neg h2, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => e.rot_b_ne_a G (Subtype.ext hc),
        fun hc => h2 (Subtype.ext hc)⟩
  · rw [if_neg h1]
    by_cases h3 : G.rot x = e.b G
    · rw [if_pos h3]
      by_cases h4 : G.rot e.a = e.a
      · rw [if_pos h4, e.mem_live G]
        exact ⟨Finset.coe_mem _,
          fun hc => e.rot_b_ne_a G (Subtype.ext hc),
          fun hc => hxb' (G.rot.injective (h3.trans (Subtype.ext hc).symm))⟩
      · rw [if_neg h4, e.mem_live G]
        exact ⟨Finset.coe_mem _,
          fun hc => h4 (Subtype.ext hc),
          fun hc => e.rot_a_ne_b G (Subtype.ext hc)⟩
    · rw [if_neg h3, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => h1 (Subtype.ext hc),
        fun hc => h3 (Subtype.ext hc)⟩

theorem stepRotInvFun_mem_live (y : ↥s) (hy : (↑y : D) ∈ e.live G) :
    (↑(G.stepRotInvFun e y) : D) ∈ e.live G := by
  obtain ⟨-, hya, hyb⟩ := (e.mem_live G ↑y).mp hy
  have hya' : y ≠ e.a := fun h => hya (congrArg _ h)
  have hyb' : y ≠ e.b G := fun h => hyb (congrArg _ h)
  unfold stepRotInvFun
  by_cases h1 : G.rot.symm y = e.a
  · rw [if_pos h1]
    by_cases h2 : G.rot.symm (e.b G) = e.b G
    · rw [if_pos h2, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => hya' (G.rot.symm.injective (h1.trans (Subtype.ext hc).symm)),
        fun hc => e.symm_a_ne_b G (Subtype.ext hc)⟩
    · rw [if_neg h2, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => e.symm_b_ne_a G (Subtype.ext hc),
        fun hc => h2 (Subtype.ext hc)⟩
  · rw [if_neg h1]
    by_cases h3 : G.rot.symm y = e.b G
    · rw [if_pos h3]
      by_cases h4 : G.rot.symm e.a = e.a
      · rw [if_pos h4, e.mem_live G]
        exact ⟨Finset.coe_mem _,
          fun hc => e.symm_b_ne_a G (Subtype.ext hc),
          fun hc => hyb' (G.rot.symm.injective (h3.trans (Subtype.ext hc).symm))⟩
      · rw [if_neg h4, e.mem_live G]
        exact ⟨Finset.coe_mem _,
          fun hc => h4 (Subtype.ext hc),
          fun hc => e.symm_a_ne_b G (Subtype.ext hc)⟩
    · rw [if_neg h3, e.mem_live G]
      exact ⟨Finset.coe_mem _,
        fun hc => h1 (Subtype.ext hc),
        fun hc => h3 (Subtype.ext hc)⟩

theorem stepRotInvFun_stepRotFun (x : ↥s) (hx : (↑x : D) ∈ e.live G) :
    G.stepRotInvFun e (G.stepRotFun e x) = x := by
  obtain ⟨-, hxa, hxb⟩ := (e.mem_live G ↑x).mp hx
  have hxa' : x ≠ e.a := fun h => hxa (congrArg _ h)
  have hxb' : x ≠ e.b G := fun h => hxb (congrArg _ h)
  unfold stepRotFun
  by_cases h1 : G.rot x = e.a
  · have hsa : G.rot.symm e.a = x := G.rot.injective (by rw [Equiv.apply_symm_apply, h1])
    rw [if_pos h1]
    by_cases h2 : G.rot (e.b G) = e.b G
    · have hsb : G.rot.symm (e.b G) = e.b G :=
        G.rot.injective (by rw [Equiv.apply_symm_apply, h2])
      rw [if_pos h2]
      unfold stepRotInvFun
      rw [if_pos (by rw [Equiv.symm_apply_apply]), if_pos hsb, hsa]
    · have hsb : G.rot.symm (e.b G) ≠ e.b G := fun h =>
        h2 (by conv_lhs => rw [← h, Equiv.apply_symm_apply])
      rw [if_neg h2]
      unfold stepRotInvFun
      rw [if_neg (by rw [Equiv.symm_apply_apply]; exact (e.a_ne_b G).symm),
        if_pos (by rw [Equiv.symm_apply_apply]),
        if_neg (by rw [hsa]; exact hxa'), hsa]
  · rw [if_neg h1]
    by_cases h3 : G.rot x = e.b G
    · have hsb : G.rot.symm (e.b G) = x := G.rot.injective (by rw [Equiv.apply_symm_apply, h3])
      rw [if_pos h3]
      by_cases h4 : G.rot e.a = e.a
      · have hsa : G.rot.symm e.a = e.a := G.rot.injective (by rw [Equiv.apply_symm_apply, h4])
        rw [if_pos h4]
        unfold stepRotInvFun
        rw [if_neg (by rw [Equiv.symm_apply_apply]; exact (e.a_ne_b G).symm),
          if_pos (by rw [Equiv.symm_apply_apply]), if_pos hsa, hsb]
      · rw [if_neg h4]
        unfold stepRotInvFun
        rw [if_pos (by rw [Equiv.symm_apply_apply]),
          if_neg (by rw [hsb]; exact hxb'), hsb]
    · rw [if_neg h3]
      unfold stepRotInvFun
      rw [if_neg (by rw [Equiv.symm_apply_apply]; exact hxa'),
        if_neg (by rw [Equiv.symm_apply_apply]; exact hxb'),
        Equiv.symm_apply_apply]

theorem stepRotFun_stepRotInvFun (y : ↥s) (hy : (↑y : D) ∈ e.live G) :
    G.stepRotFun e (G.stepRotInvFun e y) = y := by
  obtain ⟨-, hya, hyb⟩ := (e.mem_live G ↑y).mp hy
  have hya' : y ≠ e.a := fun h => hya (congrArg _ h)
  have hyb' : y ≠ e.b G := fun h => hyb (congrArg _ h)
  unfold stepRotInvFun
  by_cases h1 : G.rot.symm y = e.a
  · have hra : G.rot e.a = y := G.rot.symm.injective (by rw [Equiv.symm_apply_apply, h1])
    rw [if_pos h1]
    by_cases h2 : G.rot.symm (e.b G) = e.b G
    · have hrb : G.rot (e.b G) = e.b G :=
        G.rot.symm.injective (by rw [Equiv.symm_apply_apply, h2])
      rw [if_pos h2]
      unfold stepRotFun
      rw [if_pos (by rw [Equiv.apply_symm_apply]), if_pos hrb, hra]
    · rw [if_neg h2]
      unfold stepRotFun
      rw [if_neg (by rw [Equiv.apply_symm_apply]; exact (e.a_ne_b G).symm),
        if_pos (by rw [Equiv.apply_symm_apply]),
        if_neg (by rw [hra]; exact hya'), hra]
  · rw [if_neg h1]
    by_cases h3 : G.rot.symm y = e.b G
    · have hrb : G.rot (e.b G) = y := G.rot.symm.injective (by rw [Equiv.symm_apply_apply, h3])
      rw [if_pos h3]
      by_cases h4 : G.rot.symm e.a = e.a
      · have hra : G.rot e.a = e.a := G.rot.symm.injective (by rw [Equiv.symm_apply_apply, h4])
        rw [if_pos h4]
        unfold stepRotFun
        rw [if_neg (by rw [Equiv.apply_symm_apply]; exact (e.a_ne_b G).symm),
          if_pos (by rw [Equiv.apply_symm_apply]), if_pos hra, hrb]
      · rw [if_neg h4]
        unfold stepRotFun
        rw [if_pos (by rw [Equiv.apply_symm_apply]),
          if_neg (by rw [hrb]; exact hyb'), hrb]
    · rw [if_neg h3]
      unfold stepRotFun
      rw [if_neg (by rw [Equiv.apply_symm_apply]; exact hya'),
        if_neg (by rw [Equiv.apply_symm_apply]; exact hyb'),
        Equiv.apply_symm_apply]

theorem prt_mem_live (x : ↥s) (hx : (↑x : D) ∈ e.live G) :
    (↑(G.prt x) : D) ∈ e.live G := by
  obtain ⟨-, hxa, hxb⟩ := (e.mem_live G ↑x).mp hx
  rw [e.mem_live G]
  refine ⟨Finset.coe_mem _, fun hc => ?_, fun hc => ?_⟩
  ·
    have : x = e.b G := by
      have h := congrArg G.prt (Subtype.ext hc : G.prt x = e.a)
      rw [G.prt_invol] at h
      exact h
    exact hxb (congrArg _ this)
  ·
    have : x = e.a := by
      have h := congrArg G.prt (Subtype.ext hc : G.prt x = e.b G)
      rw [G.prt_invol] at h
      unfold StepEdge.b at h
      rw [G.prt_invol] at h
      exact h
    exact hxa (congrArg _ this)

noncomputable def stepFatgraph : Fatgraph (e.live G) where
  rot :=
    { toFun := fun x => ⟨↑(G.stepRotFun e ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩),
        G.stepRotFun_mem_live e _ x.2⟩
      invFun := fun y => ⟨↑(G.stepRotInvFun e ⟨↑y, ((e.mem_live G ↑y).mp y.2).1⟩),
        G.stepRotInvFun_mem_live e _ y.2⟩
      left_inv := fun x => by
        have h := G.stepRotInvFun_stepRotFun e ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩ x.2
        have hval := congrArg Subtype.val h
        apply Subtype.ext
        exact hval
      right_inv := fun y => by
        have h := G.stepRotFun_stepRotInvFun e ⟨↑y, ((e.mem_live G ↑y).mp y.2).1⟩ y.2
        have hval := congrArg Subtype.val h
        apply Subtype.ext
        exact hval }
  prt :=
    { toFun := fun x => ⟨↑(G.prt ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩),
        G.prt_mem_live e _ x.2⟩
      invFun := fun x => ⟨↑(G.prt ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩),
        G.prt_mem_live e _ x.2⟩
      left_inv := fun x => by
        have hval := congrArg Subtype.val (G.prt_invol ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩)
        apply Subtype.ext
        exact hval
      right_inv := fun x => by
        have hval := congrArg Subtype.val (G.prt_invol ⟨↑x, ((e.mem_live G ↑x).mp x.2).1⟩)
        apply Subtype.ext
        exact hval }
  prt_invol := fun d => by
    have hval := congrArg Subtype.val (G.prt_invol ⟨↑d, ((e.mem_live G ↑d).mp d.2).1⟩)
    apply Subtype.ext
    exact hval
  prt_ne := fun d h => by
    have hval := congrArg Subtype.val h
    exact G.prt_ne ⟨↑d, ((e.mem_live G ↑d).mp d.2).1⟩ (Subtype.ext hval)

theorem stepFatgraph_facePerm (x : ↥(e.live G)) (hx : (↑x : D) ∈ s) :
    ((↑((G.stepFatgraph e).facePerm x) : D) = ↑(G.facePerm ⟨↑x, hx⟩)
        ∧ (↑(G.facePerm ⟨↑x, hx⟩) : D) ∈ e.live G)
    ∨ ((↑(G.facePerm ⟨↑x, hx⟩) : D) ∉ e.live G
        ∧ (↑((G.stepFatgraph e).facePerm x) : D) = ↑(G.facePerm (G.facePerm ⟨↑x, hx⟩))
        ∧ (↑(G.facePerm (G.facePerm ⟨↑x, hx⟩)) : D) ∈ e.live G)
    ∨ ((↑(G.facePerm ⟨↑x, hx⟩) : D) ∉ e.live G
        ∧ (↑(G.facePerm (G.facePerm ⟨↑x, hx⟩)) : D) ∉ e.live G
        ∧ (↑((G.stepFatgraph e).facePerm x) : D)
            = ↑(G.facePerm (G.facePerm (G.facePerm ⟨↑x, hx⟩)))
        ∧ (↑(G.facePerm (G.facePerm (G.facePerm ⟨↑x, hx⟩))) : D) ∈ e.live G) := by
  classical
  have hu : (↑(G.prt ⟨↑x, hx⟩) : D) ∈ e.live G := G.prt_mem_live e ⟨↑x, hx⟩ x.2
  obtain ⟨-, hua, hub⟩ := (e.mem_live G ↑(G.prt ⟨↑x, hx⟩)).mp hu
  have hfp' : (↑((G.stepFatgraph e).facePerm x) : D)
      = ↑(G.stepRotFun e (G.prt ⟨↑x, hx⟩)) := rfl
  have hfp : G.facePerm ⟨↑x, hx⟩ = G.rot (G.prt ⟨↑x, hx⟩) := rfl
  have hprta : G.prt e.a = e.b G := rfl
  have hprtb : G.prt (e.b G) = e.a := G.prt_invol e.d₀
  by_cases hra : G.rot (G.prt ⟨↑x, hx⟩) = e.a
  · have hfpx_not : (↑(G.facePerm ⟨↑x, hx⟩) : D) ∉ e.live G := by
      rw [hfp, hra]
      intro hc
      exact ((e.mem_live G _).mp hc).2.1 rfl
    have hfp2 : G.facePerm (G.facePerm ⟨↑x, hx⟩) = G.rot (e.b G) := by
      rw [hfp, hra]
      show G.rot (G.prt e.a) = G.rot (e.b G)
      rw [hprta]
    by_cases hrb : G.rot (e.b G) = e.b G
    · have hfp3 : G.facePerm (G.facePerm (G.facePerm ⟨↑x, hx⟩)) = G.rot e.a := by
        rw [hfp2, hrb]
        show G.rot (G.prt (e.b G)) = G.rot e.a
        rw [hprtb]
      refine Or.inr (Or.inr ⟨hfpx_not, ?_, ?_, ?_⟩)
      · rw [hfp2, hrb]
        intro hc
        exact ((e.mem_live G _).mp hc).2.2 rfl
      · rw [hfp', hfp3]
        unfold stepRotFun
        rw [if_pos hra, if_pos hrb]
      · rw [hfp3, e.mem_live G]
        refine ⟨Finset.coe_mem _, fun hc => ?_,
          fun hc => e.rot_a_ne_b G (Subtype.ext hc)⟩
        exact hua (congrArg _ (G.rot.injective (hra.trans (Subtype.ext hc).symm)))
    · refine Or.inr (Or.inl ⟨hfpx_not, ?_, ?_⟩)
      · rw [hfp', hfp2]
        unfold stepRotFun
        rw [if_pos hra, if_neg hrb]
      · rw [hfp2, e.mem_live G]
        exact ⟨Finset.coe_mem _, fun hc => e.rot_b_ne_a G (Subtype.ext hc),
          fun hc => hrb (Subtype.ext hc)⟩
  · by_cases hrb' : G.rot (G.prt ⟨↑x, hx⟩) = e.b G
    · have hfpx_not : (↑(G.facePerm ⟨↑x, hx⟩) : D) ∉ e.live G := by
        rw [hfp, hrb']
        intro hc
        exact ((e.mem_live G _).mp hc).2.2 rfl
      have hfp2 : G.facePerm (G.facePerm ⟨↑x, hx⟩) = G.rot e.a := by
        rw [hfp, hrb']
        show G.rot (G.prt (e.b G)) = G.rot e.a
        rw [hprtb]
      by_cases hra' : G.rot e.a = e.a
      · have hfp3 : G.facePerm (G.facePerm (G.facePerm ⟨↑x, hx⟩)) = G.rot (e.b G) := by
          rw [hfp2, hra']
          show G.rot (G.prt e.a) = G.rot (e.b G)
          rw [hprta]
        refine Or.inr (Or.inr ⟨hfpx_not, ?_, ?_, ?_⟩)
        · rw [hfp2, hra']
          intro hc
          exact ((e.mem_live G _).mp hc).2.1 rfl
        · rw [hfp', hfp3]
          unfold stepRotFun
          rw [if_neg hra, if_pos hrb', if_pos hra']
        · rw [hfp3, e.mem_live G]
          refine ⟨Finset.coe_mem _, fun hc => e.rot_b_ne_a G (Subtype.ext hc), fun hc => ?_⟩
          exact hub (congrArg _ (G.rot.injective (hrb'.trans (Subtype.ext hc).symm)))
      · refine Or.inr (Or.inl ⟨hfpx_not, ?_, ?_⟩)
        · rw [hfp', hfp2]
          unfold stepRotFun
          rw [if_neg hra, if_pos hrb', if_neg hra']
        · rw [hfp2, e.mem_live G]
          exact ⟨Finset.coe_mem _, fun hc => hra' (Subtype.ext hc),
            fun hc => e.rot_a_ne_b G (Subtype.ext hc)⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hfp', hfp]
        unfold stepRotFun
        rw [if_neg hra, if_neg hrb']
      · rw [hfp, e.mem_live G]
        exact ⟨Finset.coe_mem _, fun hc => hra (Subtype.ext hc),
          fun hc => hrb' (Subtype.ext hc)⟩

end Fatgraph
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

inductive ContractionSeq : (s : Finset D) → Fatgraph s → (t : Finset D) → Fatgraph t → Prop
  | nil (s : Finset D) (G : Fatgraph s) : ContractionSeq s G s G
  | cons (s : Finset D) (G : Fatgraph s) (e : G.StepEdge) (t : Finset D) (H : Fatgraph t)
      (htail : ContractionSeq (e.live G) (G.stepFatgraph e) t H) : ContractionSeq s G t H

namespace Fatgraph

theorem exists_chordDiagram_of_involution (n : ℕ) (π : Equiv.Perm (Fin (2 * n)))
    (hinv : ∀ k, π (π k) = k) (hne : ∀ k, π k ≠ k) :
    ∃ Dg : _root_.PDPairing.Chord.ChordDiagram n, ∀ k, Dg.partner k = π k := by
  classical
  set P : Finset (Fin (2 * n)) := Finset.univ.filter (fun k => k < π k) with hPdef
  have hmemP : ∀ k, k ∈ P ↔ k < π k := by
    intro k
    rw [hPdef, Finset.mem_filter]
    simp
  have hcard : P.card = n := by
    have hbij : (Finset.univ.filter (fun k => π k < k)).card = P.card := by
      apply Finset.card_bij (fun k _ => π k)
      · intro k hk
        rw [Finset.mem_filter] at hk
        rw [hmemP]
        rw [hinv]
        exact hk.2
      · intro k₁ hk₁ k₂ hk₂ h
        exact π.injective h
      · intro k hk
        refine ⟨π k, ?_, hinv k⟩
        rw [Finset.mem_filter]
        rw [hmemP] at hk
        exact ⟨Finset.mem_univ _, by rw [hinv]; exact hk⟩
    have hsplit : P.card + (Finset.univ.filter (fun k => π k < k)).card = 2 * n := by
      rw [← Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_filter]
        intro k _ h1 h2
        exact absurd (h1.trans h2) (lt_irrefl k))]
      rw [show (Finset.univ.filter (fun k => k < π k))
            ∪ (Finset.univ.filter (fun k => π k < k)) = Finset.univ from ?_]
      · rw [Finset.card_univ, Fintype.card_fin]
      · refine Finset.eq_univ_of_forall fun k => ?_
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases lt_or_gt_of_ne (Ne.symm (hne k)) with h | h
        · exact Or.inl ⟨Finset.mem_univ _, h⟩
        · exact Or.inr ⟨Finset.mem_univ _, h⟩
    omega
  set c : Fin n ≃o {x // x ∈ P} := P.orderIsoOfFin hcard with hcdef
  have hcP : ∀ i : Fin n, (↑(c i) : Fin (2 * n)) ∈ P := fun i => (c i).2
  have hdartFun : Function.Bijective (fun z : Fin n ⊕ Fin n =>
      Sum.elim (fun i => (↑(c i) : Fin (2 * n))) (fun i => π ↑(c i)) z) := by
    constructor
    · intro z₁ z₂ h
      match z₁, z₂ with
      | Sum.inl i, Sum.inl j =>
        simp only [Sum.elim_inl] at h
        exact congrArg Sum.inl (c.injective (Subtype.ext h))
      | Sum.inr i, Sum.inr j =>
        simp only [Sum.elim_inr] at h
        exact congrArg Sum.inr (c.injective (Subtype.ext (π.injective h)))
      | Sum.inl i, Sum.inr j =>
        simp only [Sum.elim_inl, Sum.elim_inr] at h
        exfalso
        have h1 : (↑(c i) : Fin (2 * n)) < π ↑(c i) := (hmemP _).mp (hcP i)
        have h2 : (↑(c j) : Fin (2 * n)) < π ↑(c j) := (hmemP _).mp (hcP j)
        rw [h] at h1
        rw [hinv] at h1
        exact absurd (h2.trans h1) (lt_irrefl _)
      | Sum.inr i, Sum.inl j =>
        simp only [Sum.elim_inl, Sum.elim_inr] at h
        exfalso
        have h1 : (↑(c i) : Fin (2 * n)) < π ↑(c i) := (hmemP _).mp (hcP i)
        have h2 : (↑(c j) : Fin (2 * n)) < π ↑(c j) := (hmemP _).mp (hcP j)
        rw [← h] at h2
        rw [hinv] at h2
        exact absurd (h1.trans h2) (lt_irrefl _)
    · intro k
      by_cases hk : k ∈ P
      · exact ⟨Sum.inl (c.symm ⟨k, hk⟩), by simp⟩
      · have hπk : π k ∈ P := by
          rw [hmemP, hinv]
          rcases lt_or_gt_of_ne (Ne.symm (hne k)) with h | h
          · exact absurd ((hmemP k).mpr h) hk
          · exact h
        refine ⟨Sum.inr (c.symm ⟨π k, hπk⟩), ?_⟩
        simp only [Sum.elim_inr]
        rw [show ((c (c.symm ⟨π k, hπk⟩) : {x // x ∈ P}) : Fin (2 * n)) = π k from by
          rw [OrderIso.apply_symm_apply]]
        exact hinv k
  refine ⟨⟨Equiv.ofBijective _ hdartFun⟩, fun k => ?_⟩
  show (Equiv.ofBijective _ hdartFun)
    (Equiv.sumComm (Fin n) (Fin n) ((Equiv.ofBijective _ hdartFun).symm k)) = π k
  rcases hz : (Equiv.ofBijective _ hdartFun).symm k with i | i
  · have hk : (Equiv.ofBijective _ hdartFun) (Sum.inl i) = k := by rw [← hz]; simp
    simp only [Equiv.sumComm_apply, Sum.swap_inl]
    have : (Equiv.ofBijective _ hdartFun) (Sum.inr i) = π ↑(c i) := rfl
    rw [this]
    have hk' : (↑(c i) : Fin (2 * n)) = k := hk
    rw [hk']
  · have hk : (Equiv.ofBijective _ hdartFun) (Sum.inr i) = k := by rw [← hz]; simp
    simp only [Equiv.sumComm_apply, Sum.swap_inr]
    have : (Equiv.ofBijective _ hdartFun) (Sum.inl i) = ↑(c i) := rfl
    rw [this]
    have hk' : π ↑(c i) = k := hk
    rw [← hk', hinv]

theorem perm_pow_apply' {α : Type*} (σ : Equiv.Perm α) (k : ℕ) (x : α) :
    (σ ^ k) x = (⇑σ)^[k] x := by
  induction k with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    show σ ((σ ^ t) x) = σ ((⇑σ)^[t] x)
    rw [ih]

theorem exists_chordDiagram {t : Finset D} (H : Fatgraph t) (n : ℕ) (hn : 0 < n)
    (hcard : t.card = 2 * n) (hone : ∀ d f : ↥t, H.SameVertex d f) :
    ∃ (Dg : _root_.PDPairing.Chord.ChordDiagram n) (φ : ↥t ≃ Fin (2 * n)),
      (∀ d, φ (H.rot d) = finRotate (2 * n) (φ d))
      ∧ (∀ d, φ (H.prt d) = Dg.partner (φ d)) := by
  classical
  have h2n : 0 < 2 * n := by omega
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hnemp : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d₀v, hd₀⟩ := hnemp
  haveI : Fintype ↥t := FinsetCoe.fintype t
  set d₀ : ↥t := ⟨d₀v, hd₀⟩ with hd₀def
  have hper : d₀ ∈ Function.periodicPts ⇑H.rot := by
    refine ⟨orderOf H.rot, orderOf_pos _, ?_⟩
    show Function.IsPeriodicPt _ _ _
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← perm_pow_apply', pow_orderOf_eq_one]
    rfl
  have hmpos : 0 < Function.minimalPeriod (⇑H.rot) d₀ :=
    Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hsurj : ∀ f : ↥t, ∃ k, k < Function.minimalPeriod (⇑H.rot) d₀ ∧ (H.rot ^ k) d₀ = f := by
    intro f
    obtain ⟨i, -, hi⟩ := (hone d₀ f).exists_pow_eq'
    refine ⟨i % Function.minimalPeriod (⇑H.rot) d₀, Nat.mod_lt _ hmpos, ?_⟩
    rw [perm_pow_apply', Function.iterate_mod_minimalPeriod_eq, ← perm_pow_apply', hi]
  have hinj : ∀ k₁ k₂, k₁ < Function.minimalPeriod (⇑H.rot) d₀
      → k₂ < Function.minimalPeriod (⇑H.rot) d₀
      → (H.rot ^ k₁) d₀ = (H.rot ^ k₂) d₀ → k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂ h
    rw [perm_pow_apply', perm_pow_apply'] at h
    exact Function.iterate_injOn_Iio_minimalPeriod
      (Set.mem_Iio.mpr h₁) (Set.mem_Iio.mpr h₂) h
  have hm2n : Function.minimalPeriod (⇑H.rot) d₀ = 2 * n := by
    have himg : (Finset.range (Function.minimalPeriod (⇑H.rot) d₀)).image
        (fun k => (H.rot ^ k) d₀) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun f => ?_
      obtain ⟨k, hk, hkf⟩ := hsurj f
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hkf⟩
    calc Function.minimalPeriod (⇑H.rot) d₀
        = (Finset.range (Function.minimalPeriod (⇑H.rot) d₀)).card :=
          (Finset.card_range _).symm
      _ = ((Finset.range (Function.minimalPeriod (⇑H.rot) d₀)).image
            (fun k => (H.rot ^ k) d₀)).card :=
          (Finset.card_image_of_injOn (fun a ha b hb h =>
            hinj a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h)).symm
      _ = (Finset.univ : Finset ↥t).card := by rw [himg]
      _ = Fintype.card ↥t := Finset.card_univ
      _ = t.card := Fintype.card_coe t
      _ = 2 * n := hcard
  have hgbij : Function.Bijective (fun k : Fin (2 * n) => (H.rot ^ (k : ℕ)) d₀) := by
    constructor
    · intro k₁ k₂ h
      exact Fin.ext (hinj _ _ (by rw [hm2n]; exact k₁.isLt) (by rw [hm2n]; exact k₂.isLt) h)
    · intro f
      obtain ⟨k, hk, hkf⟩ := hsurj f
      exact ⟨⟨k, by rw [← hm2n]; exact hk⟩, hkf⟩
  set gE : Fin (2 * n) ≃ ↥t := Equiv.ofBijective _ hgbij with hgEdef
  have hgE : ∀ k : Fin (2 * n), gE k = (H.rot ^ (k : ℕ)) d₀ := fun k => rfl
  have hone' : ((1 : Fin (2 * n))).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hiter : ∀ j, (⇑H.rot)^[j % (2 * n)] d₀ = (⇑H.rot)^[j] d₀ := by
    intro j
    rw [← hm2n]
    exact Function.iterate_mod_minimalPeriod_eq
  have hgrot : ∀ k : Fin (2 * n), gE (k + 1) = H.rot (gE k) := by
    intro k
    rw [hgE, hgE]
    have hval : ((k + 1 : Fin (2 * n)) : ℕ) = ((k : ℕ) + 1) % (2 * n) := by
      rw [Fin.val_add, hone']
    rw [hval, perm_pow_apply', hiter, Function.iterate_succ_apply', ← perm_pow_apply']
  set φ : ↥t ≃ Fin (2 * n) := gE.symm with hφdef
  set π : Equiv.Perm (Fin (2 * n)) := (φ.symm.trans (H.prt.trans φ) : Fin (2 * n) ≃ Fin (2 * n))
    with hπdef
  have hπ : ∀ k, π k = φ (H.prt (φ.symm k)) := fun k => rfl
  have hπinv : ∀ k, π (π k) = k := by
    intro k
    rw [hπ, hπ, Equiv.symm_apply_apply, H.prt_invol, Equiv.apply_symm_apply]
  have hπne : ∀ k, π k ≠ k := by
    intro k hk
    rw [hπ] at hk
    have : H.prt (φ.symm k) = φ.symm k := by
      have := congrArg φ.symm hk
      rwa [Equiv.symm_apply_apply] at this
    exact H.prt_ne _ this
  obtain ⟨Dg, hDg⟩ := exists_chordDiagram_of_involution n π hπinv hπne
  refine ⟨Dg, φ, ?_, ?_⟩
  · intro d
    haveI : NeZero (2 * n) := ⟨by omega⟩
    have hd : H.rot d = gE (φ d + 1) := by
      rw [hgrot (φ d)]
      rw [show gE (φ d) = d from Equiv.apply_symm_apply gE d]
    rw [hd]
    rw [show φ (gE (φ d + 1)) = φ d + 1 from Equiv.symm_apply_apply gE _]
    rw [finRotate_apply]
  · intro d
    rw [hDg]
    rw [hπ, Equiv.symm_apply_apply]

end Fatgraph
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section MTransport

variable {D : Type*}

theorem Fatgraph.chordFace_equivariant {t : Finset D} (H : Fatgraph t) {n : ℕ}
    (Dg : PDPairing.Chord.ChordDiagram n) (φ : ↥t ≃ Fin (2 * n))
    (hrot : ∀ d, φ (H.rot d) = finRotate (2 * n) (φ d))
    (hpart : ∀ d, φ (H.prt d) = Dg.partner (φ d)) (x : ↥t) :
    φ (H.facePerm x) = (Dg.partner.trans (finRotate (2 * n))) (φ x) := by
  show φ ((H.rot * H.prt) x) = _
  rw [Equiv.Perm.mul_apply, hrot, hpart]
  rfl

theorem Fatgraph.chordFace_equivariant_pow {t : Finset D} (H : Fatgraph t) {n : ℕ}
    (Dg : PDPairing.Chord.ChordDiagram n) (φ : ↥t ≃ Fin (2 * n))
    (hrot : ∀ d, φ (H.rot d) = finRotate (2 * n) (φ d))
    (hpart : ∀ d, φ (H.prt d) = Dg.partner (φ d)) (k : ℕ) (x : ↥t) :
    φ ((H.facePerm ^ k) x) = ((Dg.partner.trans (finRotate (2 * n))) ^ k) (φ x) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
      H.chordFace_equivariant Dg φ hrot hpart, ih]

theorem Fatgraph.chordFace_minimalPeriod {t : Finset D} (H : Fatgraph t) {n : ℕ}
    (Dg : PDPairing.Chord.ChordDiagram n) (φ : ↥t ≃ Fin (2 * n))
    (hrot : ∀ d, φ (H.rot d) = finRotate (2 * n) (φ d))
    (hpart : ∀ d, φ (H.prt d) = Dg.partner (φ d)) (x : ↥t) :
    Function.minimalPeriod (⇑(Dg.partner.trans (finRotate (2 * n)))) (φ x)
      = Function.minimalPeriod (⇑H.facePerm) x := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro k
  simp only [Function.IsPeriodicPt, Function.IsFixedPt]
  rw [← perm_pow_apply', ← perm_pow_apply',
    ← H.chordFace_equivariant_pow Dg φ hrot hpart]
  exact ⟨fun h => by simpa using φ.injective h, fun h => by rw [h]⟩

theorem Fatgraph.chordFace_sameCycle_iff {t : Finset D} (H : Fatgraph t) {n : ℕ}
    (Dg : PDPairing.Chord.ChordDiagram n) (φ : ↥t ≃ Fin (2 * n))
    (hrot : ∀ d, φ (H.rot d) = finRotate (2 * n) (φ d))
    (hpart : ∀ d, φ (H.prt d) = Dg.partner (φ d)) (x y : ↥t) :
    Equiv.Perm.SameCycle (Dg.partner.trans (finRotate (2 * n))) (φ x) (φ y)
      ↔ Equiv.Perm.SameCycle H.facePerm x y := by
  constructor
  · intro hs
    obtain ⟨i, -, hi⟩ := hs.exists_pow_eq'
    rw [← H.chordFace_equivariant_pow Dg φ hrot hpart] at hi
    exact ⟨(i : ℤ), by rw [zpow_natCast, φ.injective hi]⟩
  · intro hs
    obtain ⟨i, -, hi⟩ := hs.exists_pow_eq'
    refine ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast, ← H.chordFace_equivariant_pow Dg φ hrot hpart, hi]

end MTransport
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

end PDPairing.Cover
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

namespace PDPairing
namespace Cover

abbrev CoverDart (m : ℕ) := Fin m × Fin 4

def coverPrtFun (m : ℕ) (pa pb : Equiv.Perm (Fin m)) : CoverDart m → CoverDart m :=
  fun d =>
    if d.2 = 0 then (pa d.1, 1)
    else if d.2 = 1 then (pa.symm d.1, 0)
    else if d.2 = 2 then (pb.symm d.1, 3)
    else (pb d.1, 2)

theorem coverPrtFun_involutive (m : ℕ) (pa pb : Equiv.Perm (Fin m)) :
    Function.Involutive (coverPrtFun m pa pb) := by
  intro d
  obtain ⟨v, s⟩ := d
  unfold coverPrtFun
  fin_cases s <;> simp

noncomputable def coverFatgraph (m : ℕ) (pa pb : Equiv.Perm (Fin m)) :
    Fatgraph (Finset.univ : Finset (CoverDart m)) where
  rot := Equiv.Perm.subtypePerm ((Equiv.refl (Fin m)).prodCongr (finRotate 4).symm)
    (fun x => by simp)
  prt := Equiv.Perm.subtypePerm ((coverPrtFun_involutive m pa pb).toPerm)
    (fun x => by simp)
  prt_invol := by
    intro d
    apply Subtype.ext
    have h := coverPrtFun_involutive m pa pb ↑d
    exact h
  prt_ne := by
    intro d
    obtain ⟨⟨v, sl⟩, hd⟩ := d
    intro h
    have h2 := congrArg Subtype.val h
    have hval : coverPrtFun m pa pb (v, sl) = ((v, sl) : CoverDart m) := h2
    unfold coverPrtFun at hval
    fin_cases sl <;> simp_all

theorem coverFatgraph_rot_pow_val (m : ℕ) (pa pb : Equiv.Perm (Fin m)) (k : ℕ)
    (d : ↥(Finset.univ : Finset (CoverDart m))) :
    (↑(((coverFatgraph m pa pb).rot ^ k) d) : CoverDart m)
      = ((↑d : CoverDart m).1, (((finRotate 4).symm) ^ k) (↑d : CoverDart m).2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hrot : ∀ z : ↥(Finset.univ : Finset (CoverDart m)),
        (↑((coverFatgraph m pa pb).rot z) : CoverDart m)
          = ((↑z : CoverDart m).1, (finRotate 4).symm (↑z : CoverDart m).2) := fun _ => rfl
    rw [hrot, ih, pow_succ', Equiv.Perm.mul_apply]

theorem coverFatgraph_sameVertex_iff (m : ℕ) (pa pb : Equiv.Perm (Fin m))
    (d f : ↥(Finset.univ : Finset (CoverDart m))) :
    (coverFatgraph m pa pb).SameVertex d f ↔ (↑d : CoverDart m).1 = (↑f : CoverDart m).1 := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
    have hv := congrArg (fun z : CoverDart m => z.1) (congrArg Subtype.val hi)
    rw [coverFatgraph_rot_pow_val] at hv
    exact hv
  · intro hvf
    obtain ⟨⟨v, sl⟩, hd⟩ := d
    obtain ⟨⟨w, sl'⟩, hf⟩ := f
    simp only at hvf
    have hslot : ∃ k : ℕ, (((finRotate 4).symm) ^ k) sl = sl' := by
      fin_cases sl <;> fin_cases sl' <;>
        first
        | exact ⟨0, by decide⟩
        | exact ⟨1, by decide⟩
        | exact ⟨2, by decide⟩
        | exact ⟨3, by decide⟩
    obtain ⟨k, hk⟩ := hslot
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    rw [coverFatgraph_rot_pow_val]
    simp only
    rw [hk, hvf]

namespace ContractionSeq

variable {D : Type*} [DecidableEq D]

theorem live_subset {s₀ : Finset D} {G₀ : Fatgraph s₀} {t : Finset D} {H : Fatgraph t}
    (C : ContractionSeq s₀ G₀ t H) : t ⊆ s₀ := by
  induction C with
  | nil s G => exact fun d hd => hd
  | cons s G e t' H' htail ih =>
    intro d hd
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (ih hd))

end ContractionSeq
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5"

section PipeExports

variable {D : Type*} [DecidableEq D]

omit [DecidableEq D] in

theorem Fatgraph.mem_periodicPts_facePerm' {u : Finset D} (K : Fatgraph u) (z : ↥u) :
    z ∈ Function.periodicPts ⇑K.facePerm := by
  refine ⟨orderOf K.facePerm, orderOf_pos _, ?_⟩
  show Function.IsPeriodicPt _ _ _
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← perm_pow_apply', pow_orderOf_eq_one]
  rfl

section E3Step

variable {t : Finset D} (H : Fatgraph t) (e : H.StepEdge)

def Fatgraph.liftLive (x : ↥(e.live H)) : ↥t := ⟨↑x, ((e.mem_live H ↑x).mp x.2).1⟩

@[scoped simp]
theorem Fatgraph.liftLive_val (x : ↥(e.live H)) : (↑(H.liftLive e x) : D) = ↑x := rfl

p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph"
theorem Fatgraph.liftLive_injective : Function.Injective (H.liftLive e) := by
  intro x y h
  have h2 := congrArg Subtype.val h
  exact Subtype.ext h2

theorem Fatgraph.eq_deleted_of_not_live (d : ↥t) (hd : (↑d : D) ∉ e.live H) :
    (↑d : D) = ↑e.a ∨ (↑d : D) = ↑(e.b H) := by
  by_contra hc
  rw [not_or] at hc
  exact hd ((e.mem_live H ↑d).mpr ⟨d.2, hc.1, hc.2⟩)

noncomputable def Fatgraph.stepLen (x : ↥(e.live H)) : ℕ :=
  if (↑(H.facePerm (H.liftLive e x)) : D) ∈ e.live H then 1
  else if (↑(H.facePerm (H.facePerm (H.liftLive e x))) : D) ∈ e.live H then 2
  else 3

theorem Fatgraph.stepLen_pos (x : ↥(e.live H)) : 0 < H.stepLen e x := by
  unfold stepLen
  split_ifs <;> omega

theorem Fatgraph.stepLen_le (x : ↥(e.live H)) : H.stepLen e x ≤ 3 := by
  unfold stepLen
  split_ifs <;> omega

theorem Fatgraph.stepLen_spec (x : ↥(e.live H)) :
    (H.facePerm ^ (H.stepLen e x)) (H.liftLive e x)
        = H.liftLive e ((H.stepFatgraph e).facePerm x)
    ∧ ∀ i, 0 < i → i < H.stepLen e x →
        (↑((H.facePerm ^ i) (H.liftLive e x)) : D) ∉ e.live H := by
  have hsq : ∀ z : ↥t, (H.facePerm ^ 2) z = H.facePerm (H.facePerm z) := by
    intro z
    rw [sq]
    rfl
  have hcb : ∀ z : ↥t, (H.facePerm ^ 3) z = H.facePerm (H.facePerm (H.facePerm z)) := by
    intro z
    rw [pow_succ, sq]
    rfl
  rcases H.stepFatgraph_facePerm e x (((e.mem_live H ↑x).mp x.2).1) with
    ⟨heq, hlive⟩ | ⟨hnot1, heq, hlive⟩ | ⟨hnot1, hnot2, heq, hlive⟩
  · have hL : H.stepLen e x = 1 := by
      unfold stepLen
      split_ifs with h1 h2
      · rfl
      · exact absurd hlive h1
      · exact absurd hlive h1
    refine ⟨?_, fun i hi1 hi2 => by omega⟩
    rw [hL, pow_one]
    exact Subtype.ext heq.symm
  · have hL : H.stepLen e x = 2 := by
      unfold stepLen
      split_ifs with h1 h2
      · exact absurd h1 hnot1
      · rfl
      · exact absurd hlive h2
    refine ⟨?_, fun i hi1 hi2 => ?_⟩
    · rw [hL, hsq]
      exact Subtype.ext heq.symm
    · have hi : i = 1 := by omega
      rw [hi, pow_one]
      exact hnot1
  · have hL : H.stepLen e x = 3 := by
      unfold stepLen
      split_ifs with h1 h2
      · exact absurd h1 hnot1
      · exact absurd h2 hnot2
      · rfl
    refine ⟨?_, fun i hi1 hi2 => ?_⟩
    · rw [hL, hcb]
      exact Subtype.ext heq.symm
    · rcases (by omega : i = 1 ∨ i = 2) with hi | hi
      · rw [hi, pow_one]
        exact hnot1
      · rw [hi, hsq]
        exact hnot2

noncomputable def Fatgraph.sigmaIdx (x : ↥(e.live H)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sigmaIdx x j + H.stepLen e (((H.stepFatgraph e).facePerm ^ j) x)

theorem Fatgraph.sigmaIdx_zero (x : ↥(e.live H)) : H.sigmaIdx e x 0 = 0 := by
  simp [Fatgraph.sigmaIdx]

theorem Fatgraph.sigmaIdx_succ (x : ↥(e.live H)) (j : ℕ) :
    H.sigmaIdx e x (j + 1)
      = H.sigmaIdx e x j + H.stepLen e (((H.stepFatgraph e).facePerm ^ j) x) := by
  simp [Fatgraph.sigmaIdx]

theorem Fatgraph.stepLen_pos' (x : ↥(e.live H)) (j : ℕ) :
    0 < H.stepLen e (((H.stepFatgraph e).facePerm ^ j) x) :=
  H.stepLen_pos e _

theorem Fatgraph.le_sigmaIdx (x : ↥(e.live H)) (j : ℕ) : j ≤ H.sigmaIdx e x j := by
  induction j with
  | zero => omega
  | succ k ih =>
    rw [H.sigmaIdx_succ e x k]
    have := H.stepLen_pos' e x k
    omega

theorem Fatgraph.sigmaIdx_spec (x : ↥(e.live H)) (j : ℕ) :
    (H.facePerm ^ (H.sigmaIdx e x j)) (H.liftLive e x)
      = H.liftLive e (((H.stepFatgraph e).facePerm ^ j) x) := by
  induction j with
  | zero =>
    rw [H.sigmaIdx_zero e x, pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [H.sigmaIdx_succ e x k, add_comm, pow_add]
    show (H.facePerm ^ H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x))
      ((H.facePerm ^ H.sigmaIdx e x k) (H.liftLive e x)) = _
    rw [ih, (H.stepLen_spec e (((H.stepFatgraph e).facePerm ^ k) x)).1]
    congr 1
    rw [pow_succ']
    rfl

theorem Fatgraph.sigmaIdx_sum (x : ↥(e.live H)) (g : D → ℤ)
    (hga : g ↑e.a = 0) (hgb : g ↑(e.b H) = 0) (j : ℕ) :
    (∑ i ∈ Finset.range (H.sigmaIdx e x j), g ↑((H.facePerm ^ i) (H.liftLive e x)))
      = ∑ k ∈ Finset.range j, g ↑(((H.stepFatgraph e).facePerm ^ k) x) := by
  have hgdel : ∀ z : ↥t, (↑z : D) ∉ e.live H → g ↑z = 0 := by
    intro z hz
    rcases H.eq_deleted_of_not_live e z hz with h | h
    · rw [h, hga]
    · rw [h, hgb]
  have hmid : ∀ (k : ℕ) (r : ℕ), 0 < r → r < H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) →
      g ↑((H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x)) = 0 := by
    intro k r hr1 hr2
    have hpos : (H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x)
        = (H.facePerm ^ r) (H.liftLive e (((H.stepFatgraph e).facePerm ^ k) x)) := by
      rw [add_comm, pow_add]
      show (H.facePerm ^ r) ((H.facePerm ^ H.sigmaIdx e x k) (H.liftLive e x)) = _
      rw [H.sigmaIdx_spec e x k]
    rw [hpos]
    exact hgdel _ ((H.stepLen_spec e (((H.stepFatgraph e).facePerm ^ k) x)).2 r hr1 hr2)
  have hhead : ∀ k : ℕ, g ↑((H.facePerm ^ (H.sigmaIdx e x k)) (H.liftLive e x))
      = g ↑(((H.stepFatgraph e).facePerm ^ k) x) := by
    intro k
    rw [H.sigmaIdx_spec e x k, H.liftLive_val]
  induction j with
  | zero =>
    rw [H.sigmaIdx_zero e x]
    simp
  | succ k ih =>
    have hL13 : H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 1
        ∨ H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 2
        ∨ H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 3 := by
      have h1 := H.stepLen_pos' e x k
      have h2 := H.stepLen_le e (((H.stepFatgraph e).facePerm ^ k) x)
      omega
    rw [H.sigmaIdx_succ e x k, Finset.sum_range_succ]
    rcases hL13 with hL | hL | hL
    · rw [hL, Finset.sum_range_succ, ih, hhead k]
    · rw [hL, show H.sigmaIdx e x k + 2 = (H.sigmaIdx e x k + 1) + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, hhead k,
        hmid k 1 (by omega) (by omega)]
      ring
    · rw [hL, show H.sigmaIdx e x k + 3 = ((H.sigmaIdx e x k + 1) + 1) + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, hhead k,
        hmid k 1 (by omega) (by omega), hmid k 2 (by omega) (by omega)]
      ring

theorem Fatgraph.sigmaIdx_block (x : ↥(e.live H)) (J : ℕ) :
    ∀ i < H.sigmaIdx e x J,
      (∃ j < J, i = H.sigmaIdx e x j)
      ∨ (↑((H.facePerm ^ i) (H.liftLive e x)) : D) ∉ e.live H := by
  induction J with
  | zero =>
    intro i hi
    rw [H.sigmaIdx_zero e x] at hi
    omega
  | succ J ihJ =>
    intro i hi
    rw [H.sigmaIdx_succ e x J] at hi
    by_cases hiJ : i < H.sigmaIdx e x J
    · rcases ihJ i hiJ with ⟨j, hj, rfl⟩ | h
      · exact Or.inl ⟨j, by omega, rfl⟩
      · exact Or.inr h
    · by_cases hr0 : i = H.sigmaIdx e x J
      · exact Or.inl ⟨J, by omega, hr0⟩
      · refine Or.inr ?_
        obtain ⟨r, hr⟩ : ∃ r, i = r + H.sigmaIdx e x J := ⟨i - H.sigmaIdx e x J, by omega⟩
        subst hr
        have hmid : (H.facePerm ^ (r + H.sigmaIdx e x J)) (H.liftLive e x)
            = (H.facePerm ^ r)
                (H.liftLive e (((H.stepFatgraph e).facePerm ^ J) x)) := by
          rw [pow_add]
          show (H.facePerm ^ r)
            ((H.facePerm ^ H.sigmaIdx e x J) (H.liftLive e x)) = _
          rw [H.sigmaIdx_spec e x J]
        rw [hmid]
        exact (H.stepLen_spec e (((H.stepFatgraph e).facePerm ^ J) x)).2 _
          (by omega) (by omega)

theorem Fatgraph.sigmaIdx_minPer (x : ↥(e.live H)) :
    Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)
      = H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x) := by
  have hm'pos : 0 < Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      ((H.stepFatgraph e).mem_periodicPts_facePerm' x)
  have hfix' : ((H.stepFatgraph e).facePerm
      ^ (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x)) x = x := by
    rw [perm_pow_apply', Function.iterate_minimalPeriod]
  have hperiod : Function.IsPeriodicPt (⇑H.facePerm)
      (H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x))
      (H.liftLive e x) := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← perm_pow_apply',
      H.sigmaIdx_spec e x _, hfix']
  have hσpos : 0 < H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x) :=
    lt_of_lt_of_le hm'pos (H.le_sigmaIdx e x _)
  have hle : Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)
      ≤ H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x) :=
    hperiod.minimalPeriod_le hσpos
  have hppos : 0 < Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x) :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (H.mem_periodicPts_facePerm' (H.liftLive e x))
  have hpfix : (H.facePerm ^ (Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)))
      (H.liftLive e x) = H.liftLive e x := by
    rw [perm_pow_apply', Function.iterate_minimalPeriod]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    rcases H.sigmaIdx_block e x _ _ hlt with ⟨j, hj, hpj⟩ | hdead
    · have hjfix : ((H.stepFatgraph e).facePerm ^ j) x = x := by
        apply H.liftLive_injective e
        rw [← H.sigmaIdx_spec e x j, ← hpj, hpfix]
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0, H.sigmaIdx_zero e x] at hpj
        omega
      have hdvd : Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x ∣ j := by
        apply Function.IsPeriodicPt.minimalPeriod_dvd
        rw [Function.IsPeriodicPt, Function.IsFixedPt, ← perm_pow_apply', hjfix]
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · rw [hpfix] at hdead
      exact hdead (by rw [H.liftLive_val]; exact x.2)
  · exact heq

end E3Step
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph"

theorem Fatgraph.step_orbit_sum {t : Finset D} (H : Fatgraph t) (e : H.StepEdge) (g : D → ℤ)
    (hga : g ↑e.a = 0) (hgb : g ↑(e.b H) = 0) (x : ↥(e.live H)) :
    (∑ k ∈ Finset.range (Function.minimalPeriod
        (⇑(H.stepFatgraph e).facePerm) x),
      g ↑(((H.stepFatgraph e).facePerm ^ k) x))
    = ∑ k ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)),
      g ↑((H.facePerm ^ k) (H.liftLive e x)) := by
  rw [H.sigmaIdx_minPer e x]
  exact (H.sigmaIdx_sum e x g hga hgb _).symm

theorem Fatgraph.pipe_orbit_sum {s₀ : Finset D} (G₀ : Fatgraph s₀) {t : Finset D}
    {H : Fatgraph t} (C : ContractionSeq s₀ G₀ t H) :
    ∀ (g : D → ℤ), (∀ d ∈ s₀, d ∉ t → g d = 0) →
    ∀ x : ↥t,
      (∑ k ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) x),
        g ↑((H.facePerm ^ k) x))
      = ∑ k ∈ Finset.range (Function.minimalPeriod (⇑G₀.facePerm)
          ⟨↑x, C.live_subset x.2⟩),
        g ↑((G₀.facePerm ^ k) ⟨↑x, C.live_subset x.2⟩) := by
  induction C with
  | nil s G =>
    intro g hg x
    rfl
  | cons s G e t' H' htail ih =>
    intro g hg x
    have hanotlive : (↑e.a : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑e.a).mp hmem).2.1 rfl
    have hbnotlive : (↑(e.b G) : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑(e.b G)).mp hmem).2.2 rfl
    have hga : g ↑e.a = 0 :=
      hg ↑e.a (Finset.coe_mem _) (fun ht' => hanotlive (htail.live_subset ht'))
    have hgb : g ↑(e.b G) = 0 :=
      hg ↑(e.b G) (Finset.coe_mem _) (fun ht' => hbnotlive (htail.live_subset ht'))
    have hg' : ∀ d ∈ e.live G, d ∉ t' → g d = 0 := fun d hd hnt =>
      hg d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hnt
    have h1 := ih g hg' x
    have h2 := G.step_orbit_sum e g hga hgb ⟨↑x, htail.live_subset x.2⟩
    exact h1.trans h2

theorem Fatgraph.stepFatgraph_sameCycle_iff {t : Finset D} (H : Fatgraph t) (e : H.StepEdge)
    (x y : ↥(e.live H)) :
    Equiv.Perm.SameCycle (H.stepFatgraph e).facePerm x y
      ↔ Equiv.Perm.SameCycle H.facePerm (H.liftLive e x) (H.liftLive e y) := by
  constructor
  · intro hs
    obtain ⟨j, -, hj⟩ := hs.exists_pow_eq'
    refine ⟨(H.sigmaIdx e x j : ℤ), ?_⟩
    rw [zpow_natCast, H.sigmaIdx_spec e x j, hj]
  · intro hs
    obtain ⟨i, -, hi⟩ := hs.exists_pow_eq'
    have hP : Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)
        = H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x) :=
      H.sigmaIdx_minPer e x
    have hPpos : 0 < Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x) :=
      Function.minimalPeriod_pos_of_mem_periodicPts (H.mem_periodicPts_facePerm' _)
    have hmod : (H.facePerm ^ (i % Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)))
        (H.liftLive e x) = H.liftLive e y := by
      rw [Fatgraph.perm_pow_apply', Function.iterate_mod_minimalPeriod_eq,
        ← Fatgraph.perm_pow_apply', hi]
    have hlt : i % Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)
        < H.sigmaIdx e x (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x) := by
      rw [← hP]
      exact Nat.mod_lt _ hPpos
    rcases H.sigmaIdx_block e x _ _ hlt with ⟨j, hjP, hij⟩ | hdead
    · refine ⟨(j : ℤ), ?_⟩
      rw [zpow_natCast]
      apply H.liftLive_injective e
      rw [← H.sigmaIdx_spec e x j, ← hij, hmod]
    · exfalso
      rw [hmod, H.liftLive_val e y] at hdead
      exact hdead y.2

theorem Fatgraph.pipe_sameCycle_iff {s₀ : Finset D} {G₀ : Fatgraph s₀} {t : Finset D}
    {H : Fatgraph t} (C : ContractionSeq s₀ G₀ t H) (x y : ↥t) :
    ∀ (hx : (↑x : D) ∈ s₀) (hy : (↑y : D) ∈ s₀),
      Equiv.Perm.SameCycle H.facePerm x y
        ↔ Equiv.Perm.SameCycle G₀.facePerm ⟨↑x, hx⟩ ⟨↑y, hy⟩ := by
  induction C with
  | nil s G =>
    intro hx hy
    exact Iff.rfl
  | cons s G e₀ u K htail ih =>
    intro hx hy
    rw [ih x y (htail.live_subset x.2) (htail.live_subset y.2),
      G.stepFatgraph_sameCycle_iff e₀]
    exact Iff.rfl

end PipeExports
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph"

end PDPairing.Cover
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph"

namespace PDPairing
namespace Cover

variable {D : Type*} [DecidableEq D]

section MergeControl

variable {t : Finset D} (G : Fatgraph t) (e : G.StepEdge)

theorem Fatgraph.StepEdge.a_not_live : (↑e.a : D) ∉ e.live G := fun hmem =>
  ((e.mem_live G ↑e.a).mp hmem).2.1 rfl

theorem Fatgraph.StepEdge.b_not_live : (↑(e.b G) : D) ∉ e.live G := fun hmem =>
  ((e.mem_live G ↑(e.b G)).mp hmem).2.2 rfl

noncomputable def Fatgraph.StepEdge.tau : Equiv.Perm (↥t) := G.rot * Equiv.swap e.a (e.b G)

theorem Fatgraph.StepEdge.tau_apply (z : ↥t) : e.tau G z = G.rot (Equiv.swap e.a (e.b G) z) := rfl

theorem Fatgraph.StepEdge.tau_apply_of_ne (z : ↥t) (hza : z ≠ e.a) (hzb : z ≠ e.b G) :
    e.tau G z = G.rot z := by
  rw [e.tau_apply G, Equiv.swap_apply_of_ne_of_ne hza hzb]

theorem Fatgraph.StepEdge.tau_apply_a : e.tau G e.a = G.rot (e.b G) := by
  rw [e.tau_apply G, Equiv.swap_apply_left]

theorem Fatgraph.StepEdge.tau_apply_b : e.tau G (e.b G) = G.rot e.a := by
  rw [e.tau_apply G, Equiv.swap_apply_right]

theorem Fatgraph.stepRot_tau_spec (x : ↥(e.live G)) :
    ∃ k, 0 < k ∧ k ≤ 3
    ∧ (↑((G.stepFatgraph e).rot x) : D) = ↑((e.tau G ^ k) (G.liftLive e x))
    ∧ ∀ i, 0 < i → i < k → (↑((e.tau G ^ i) (G.liftLive e x)) : D) ∉ e.live G := by
  obtain ⟨-, hxa, hxb⟩ := (e.mem_live G ↑x).mp x.2
  have hxa' : G.liftLive e x ≠ e.a := fun h => hxa (congrArg Subtype.val h)
  have hxb' : G.liftLive e x ≠ e.b G := fun h => hxb (congrArg Subtype.val h)
  have hτ1' : e.tau G (G.liftLive e x) = G.rot (G.liftLive e x) :=
    e.tau_apply_of_ne G _ hxa' hxb'
  have hτ1 : (e.tau G ^ 1) (G.liftLive e x) = G.rot (G.liftLive e x) := by
    rw [pow_one]
    exact hτ1'
  have hpow2 : (e.tau G ^ 2) (G.liftLive e x) = e.tau G ((e.tau G ^ 1) (G.liftLive e x)) := by
    rw [pow_succ']
    rfl
  have hpow3 : (e.tau G ^ 3) (G.liftLive e x) = e.tau G ((e.tau G ^ 2) (G.liftLive e x)) := by
    rw [pow_succ']
    rfl
  have hvalrot : (↑((G.stepFatgraph e).rot x) : D)
      = ↑(G.stepRotFun e (G.liftLive e x)) := rfl
  by_cases h1 : G.rot (G.liftLive e x) = e.a
  · have hτ2 : (e.tau G ^ 2) (G.liftLive e x) = G.rot (e.b G) := by
      rw [hpow2, hτ1, h1, e.tau_apply_a G]
    by_cases h2 : G.rot (e.b G) = e.b G
    ·
      refine ⟨3, by omega, by omega, ?_, ?_⟩
      · have hτ3 : (e.tau G ^ 3) (G.liftLive e x) = G.rot e.a := by
          rw [hpow3, hτ2, h2, e.tau_apply_b G]
        rw [hvalrot, hτ3]
        show (↑(G.stepRotFun e (G.liftLive e x)) : D) = ↑(G.rot e.a)
        unfold stepRotFun
        split_ifs
        rfl
      · intro i hi1 hi2
        rcases (by omega : i = 1 ∨ i = 2) with hi | hi
        · rw [hi, hτ1, h1]
          exact e.a_not_live G
        · rw [hi, hτ2, h2]
          exact e.b_not_live G
    ·
      refine ⟨2, by omega, by omega, ?_, ?_⟩
      · rw [hvalrot, hτ2]
        show (↑(G.stepRotFun e (G.liftLive e x)) : D) = ↑(G.rot (e.b G))
        unfold stepRotFun
        split_ifs
        rfl
      · intro i hi1 hi2
        have hi : i = 1 := by omega
        rw [hi, hτ1, h1]
        exact e.a_not_live G
  · by_cases h3 : G.rot (G.liftLive e x) = e.b G
    · have hτ2 : (e.tau G ^ 2) (G.liftLive e x) = G.rot e.a := by
        rw [hpow2, hτ1, h3, e.tau_apply_b G]
      by_cases h4 : G.rot e.a = e.a
      ·
        refine ⟨3, by omega, by omega, ?_, ?_⟩
        · have hτ3 : (e.tau G ^ 3) (G.liftLive e x) = G.rot (e.b G) := by
            rw [hpow3, hτ2, h4, e.tau_apply_a G]
          rw [hvalrot, hτ3]
          show (↑(G.stepRotFun e (G.liftLive e x)) : D) = ↑(G.rot (e.b G))
          unfold stepRotFun
          split_ifs
          rfl
        · intro i hi1 hi2
          rcases (by omega : i = 1 ∨ i = 2) with hi | hi
          · rw [hi, hτ1, h3]
            exact e.b_not_live G
          · rw [hi, hτ2, h4]
            exact e.a_not_live G
      ·
        refine ⟨2, by omega, by omega, ?_, ?_⟩
        · rw [hvalrot, hτ2]
          show (↑(G.stepRotFun e (G.liftLive e x)) : D) = ↑(G.rot e.a)
          unfold stepRotFun
          split_ifs
          rfl
        · intro i hi1 hi2
          have hi : i = 1 := by omega
          rw [hi, hτ1, h3]
          exact e.b_not_live G
    ·
      refine ⟨1, by omega, by omega, ?_, fun i hi1 hi2 => by omega⟩
      rw [hvalrot, hτ1]
      show (↑(G.stepRotFun e (G.liftLive e x)) : D) = ↑(G.rot (G.liftLive e x))
      unfold stepRotFun
      split_ifs
      rfl

theorem Fatgraph.stepRot_pow_tau (x : ↥(e.live G)) (j : ℕ) :
    ∃ K : ℕ, (↑(((G.stepFatgraph e).rot ^ j) x) : D) = ↑((e.tau G ^ K) (G.liftLive e x)) := by
  induction j with
  | zero =>
    exact ⟨0, by rw [pow_zero, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply,
      G.liftLive_val e x]⟩
  | succ j ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨k, -, -, hval, -⟩ := G.stepRot_tau_spec e (((G.stepFatgraph e).rot ^ j) x)
    have hlift : G.liftLive e (((G.stepFatgraph e).rot ^ j) x)
        = (e.tau G ^ K) (G.liftLive e x) := Subtype.ext hK
    refine ⟨k + K, ?_⟩
    have hstep : ((G.stepFatgraph e).rot ^ (j + 1)) x
        = (G.stepFatgraph e).rot (((G.stepFatgraph e).rot ^ j) x) := by
      rw [pow_succ']
      rfl
    rw [hstep, hval, hlift, ← Equiv.Perm.mul_apply, ← pow_add]

theorem Fatgraph.tau_pow_class (z : ↥t) (K : ℕ) :
    G.SameVertex z ((e.tau G ^ K) z)
    ∨ G.SameVertex e.a ((e.tau G ^ K) z)
    ∨ G.SameVertex (e.b G) ((e.tau G ^ K) z) := by
  induction K with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply]
    exact Or.inl (Equiv.Perm.SameCycle.refl _ _)
  | succ K ih =>
    have hstep : (e.tau G ^ (K + 1)) z = e.tau G ((e.tau G ^ K) z) := by
      rw [pow_succ']
      rfl
    rw [hstep]
    have hrotstep : ∀ w : ↥t, G.SameVertex w (G.rot w) := fun w => ⟨1, by rw [zpow_one]⟩
    by_cases hwa : (e.tau G ^ K) z = e.a
    · rw [hwa, e.tau_apply_a G]
      exact Or.inr (Or.inr (hrotstep (e.b G)))
    · by_cases hwb : (e.tau G ^ K) z = e.b G
      · rw [hwb, e.tau_apply_b G]
        exact Or.inr (Or.inl (hrotstep e.a))
      · rw [e.tau_apply_of_ne G _ hwa hwb]
        rcases ih with h | h | h
        · exact Or.inl (h.trans (hrotstep _))
        · exact Or.inr (Or.inl (h.trans (hrotstep _)))
        · exact Or.inr (Or.inr (h.trans (hrotstep _)))

theorem Fatgraph.stepFatgraph_sameVertex_elim {x y : ↥(e.live G)}
    (h : (G.stepFatgraph e).SameVertex x y) :
    G.SameVertex (G.liftLive e x) (G.liftLive e y)
    ∨ ((G.SameVertex (G.liftLive e x) e.a ∨ G.SameVertex (G.liftLive e x) (e.b G))
        ∧ (G.SameVertex (G.liftLive e y) e.a ∨ G.SameVertex (G.liftLive e y) (e.b G))) := by
  obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
  obtain ⟨K, hK⟩ := G.stepRot_pow_tau e x i
  rw [hi] at hK
  have hŷ : G.liftLive e y = (e.tau G ^ K) (G.liftLive e x) := Subtype.ext hK
  have hτxy : Equiv.Perm.SameCycle (e.tau G) (G.liftLive e x) (G.liftLive e y) :=
    ⟨(K : ℤ), by rw [zpow_natCast, hŷ]⟩
  rcases G.tau_pow_class e (G.liftLive e x) K with hx0 | hx0 | hx0
  · exact Or.inl (hŷ ▸ hx0)
  ·
    obtain ⟨K', hK'⟩ := hτxy.symm.exists_pow_eq'
    rcases G.tau_pow_class e (G.liftLive e y) K' with hy0 | hy0 | hy0
    ·
      have hxy : G.SameVertex (G.liftLive e x) (G.liftLive e y) := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      exact Or.inl hxy
    · have hxa : G.SameVertex (G.liftLive e x) e.a := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      refine Or.inr ⟨Or.inl hxa, Or.inl ?_⟩
      exact (hŷ ▸ hx0).symm
    · have hxb : G.SameVertex (G.liftLive e x) (e.b G) := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      refine Or.inr ⟨Or.inr hxb, Or.inl ?_⟩
      exact (hŷ ▸ hx0).symm
  · obtain ⟨K', hK'⟩ := hτxy.symm.exists_pow_eq'
    rcases G.tau_pow_class e (G.liftLive e y) K' with hy0 | hy0 | hy0
    · have hxy : G.SameVertex (G.liftLive e x) (G.liftLive e y) := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      exact Or.inl hxy
    · have hxa : G.SameVertex (G.liftLive e x) e.a := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      refine Or.inr ⟨Or.inl hxa, Or.inr ?_⟩
      exact (hŷ ▸ hx0).symm
    · have hxb : G.SameVertex (G.liftLive e x) (e.b G) := by
        have := hy0
        rw [hK'.2] at this
        exact this.symm
      refine Or.inr ⟨Or.inr hxb, Or.inr ?_⟩
      exact (hŷ ▸ hx0).symm

omit [DecidableEq D] in

theorem Fatgraph.perm_mem_periodicPts {u : Finset D} (σ : Equiv.Perm (↥u)) (z : ↥u) :
    z ∈ Function.periodicPts ⇑σ := by
  refine ⟨orderOf σ, orderOf_pos _, ?_⟩
  show Function.IsPeriodicPt _ _ _
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Fatgraph.perm_pow_apply', pow_orderOf_eq_one]
  rfl

theorem Fatgraph.StepEdge.tau_sameCycle_rot_b_pow (k : ℕ)
    (hk : k ≤ Function.minimalPeriod (⇑G.rot) (e.b G)) (hk1 : 1 ≤ k) :
    Equiv.Perm.SameCycle (e.tau G) (G.rot (e.b G)) ((G.rot ^ k) (e.b G)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
    · rw [← h1, pow_one]
    · have hk' : 1 ≤ k := by omega
      have hkm : k ≤ Function.minimalPeriod (⇑G.rot) (e.b G) := by omega
      have hkmlt : k < Function.minimalPeriod (⇑G.rot) (e.b G) := by omega
      refine (ih hkm hk').trans ?_
      set w : ↥t := (G.rot ^ k) (e.b G) with hwdef
      have hwb : w ≠ e.b G := by
        intro hw
        have hper : Function.IsPeriodicPt (⇑G.rot) k (e.b G) := by
          rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Fatgraph.perm_pow_apply', ← hwdef, hw]
        have hdvd := hper.minimalPeriod_dvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hwa : w ≠ e.a := by
        intro hw
        apply e.hcross
        have hba : G.SameVertex (e.b G) e.a := by
          rw [← hw, hwdef]
          exact ⟨(k : ℤ), by rw [zpow_natCast]⟩
        exact hba.symm
      have hstep : (G.rot ^ (k + 1)) (e.b G) = G.rot w := by
        rw [hwdef, pow_succ']
        rfl
      rw [hstep, ← e.tau_apply_of_ne G w hwa hwb]
      exact ⟨1, by rw [zpow_one]⟩

theorem Fatgraph.StepEdge.tau_sameCycle_ab : Equiv.Perm.SameCycle (e.tau G) e.a (e.b G) := by
  have hn : 0 < Function.minimalPeriod (⇑G.rot) (e.b G) :=
    Function.minimalPeriod_pos_of_mem_periodicPts (Fatgraph.perm_mem_periodicPts G.rot (e.b G))
  have hfix : (G.rot ^ (Function.minimalPeriod (⇑G.rot) (e.b G))) (e.b G) = e.b G := by
    rw [Fatgraph.perm_pow_apply', Function.iterate_minimalPeriod]
  have h1 : Equiv.Perm.SameCycle (e.tau G) e.a (G.rot (e.b G)) := by
    refine ⟨1, ?_⟩
    rw [zpow_one, e.tau_apply_a G]
  refine h1.trans ?_
  have := e.tau_sameCycle_rot_b_pow G (Function.minimalPeriod (⇑G.rot) (e.b G)) le_rfl hn
  rw [hfix] at this
  exact this

theorem Fatgraph.StepEdge.tau_sameCycle_of_rot {z w : ↥t} (h : G.SameVertex z w) :
    Equiv.Perm.SameCycle (e.tau G) z w := by
  have hstep : ∀ v : ↥t, Equiv.Perm.SameCycle (e.tau G) v (G.rot v) := by
    intro v
    by_cases hva : v = e.a
    · subst hva

      refine (e.tau_sameCycle_ab G).trans ?_
      refine Equiv.Perm.SameCycle.trans ⟨1, by rw [zpow_one]⟩ ?_
      rw [e.tau_apply_b G]
    · by_cases hvb : v = e.b G
      · subst hvb

        refine (e.tau_sameCycle_ab G).symm.trans ?_
        refine Equiv.Perm.SameCycle.trans ⟨1, by rw [zpow_one]⟩ ?_
        rw [e.tau_apply_a G]
      · rw [← e.tau_apply_of_ne G v hva hvb]
        exact ⟨1, by rw [zpow_one]⟩
  obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
  have hpow : ∀ k : ℕ, Equiv.Perm.SameCycle (e.tau G) z ((G.rot ^ k) z) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
    | succ k ih =>
      have : (G.rot ^ (k + 1)) z = G.rot ((G.rot ^ k) z) := by
        rw [pow_succ']
        rfl
      rw [this]
      exact ih.trans (hstep _)
  rw [← hi]
  exact hpow i

theorem Fatgraph.stepRot_reaches (K : ℕ) :
    ∀ x : ↥(e.live G), (↑((e.tau G ^ K) (G.liftLive e x)) : D) ∈ e.live G →
      ∃ j : ℕ, (↑(((G.stepFatgraph e).rot ^ j) x) : D) = ↑((e.tau G ^ K) (G.liftLive e x)) := by
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
    intro x hlive
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0
      exact ⟨0, by rw [pow_zero, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply,
        G.liftLive_val e x]⟩
    · obtain ⟨k₁, hk₁pos, -, hval, hmid⟩ := G.stepRot_tau_spec e x
      by_cases hKk : K < k₁
      · exact absurd hlive (hmid K hKpos hKk)
      · obtain ⟨r, hr⟩ : ∃ r, K = r + k₁ := ⟨K - k₁, by omega⟩
        subst hr
        have hz : G.liftLive e ((G.stepFatgraph e).rot x) = (e.tau G ^ k₁) (G.liftLive e x) :=
          Subtype.ext hval
        have hsplit : (e.tau G ^ (r + k₁)) (G.liftLive e x)
            = (e.tau G ^ r) (G.liftLive e ((G.stepFatgraph e).rot x)) := by
          rw [hz, pow_add]
          rfl
        rw [hsplit] at hlive ⊢
        obtain ⟨j', hj'⟩ := ihK r (by omega) ((G.stepFatgraph e).rot x) hlive
        refine ⟨j' + 1, ?_⟩
        rw [← hj']
        congr 1

theorem Fatgraph.stepFatgraph_sameVertex_of {x y : ↥(e.live G)}
    (h : G.SameVertex (G.liftLive e x) (G.liftLive e y)) :
    (G.stepFatgraph e).SameVertex x y := by
  have hτ := e.tau_sameCycle_of_rot G h
  obtain ⟨K, -, hK⟩ := hτ.exists_pow_eq'
  have hlive : (↑((e.tau G ^ K) (G.liftLive e x)) : D) ∈ e.live G := by
    rw [hK, G.liftLive_val e y]
    exact y.2
  obtain ⟨j, hj⟩ := G.stepRot_reaches e K x hlive
  have hxy : ((G.stepFatgraph e).rot ^ j) x = y := by
    apply Subtype.ext
    rw [hj, hK, G.liftLive_val e y]
  exact ⟨(j : ℤ), by rw [zpow_natCast, hxy]⟩

theorem Fatgraph.stepFatgraph_sameVertex_join
    (x y : ↥(e.live G)) (hx : (↑x : D) = ↑(G.rot e.a)) (hy : (↑y : D) = ↑(G.rot (e.b G))) :
    (G.stepFatgraph e).SameVertex x y := by
  have hx' : G.liftLive e x = G.rot e.a := Subtype.ext hx
  have hy' : G.liftLive e y = G.rot (e.b G) := Subtype.ext hy
  have hτ : Equiv.Perm.SameCycle (e.tau G) (G.liftLive e x) (G.liftLive e y) := by
    rw [hx', hy', ← e.tau_apply_b G, ← e.tau_apply_a G]

    have h1 : Equiv.Perm.SameCycle (e.tau G) (e.tau G (e.b G)) (e.b G) := by
      refine ⟨-1, ?_⟩
      rw [zpow_neg_one]
      exact Equiv.symm_apply_apply _ _
    have h2 : Equiv.Perm.SameCycle (e.tau G) e.a (e.tau G e.a) := ⟨1, by rw [zpow_one]⟩
    exact (h1.trans (e.tau_sameCycle_ab G).symm).trans h2
  obtain ⟨K, -, hK⟩ := hτ.exists_pow_eq'
  have hlive : (↑((e.tau G ^ K) (G.liftLive e x)) : D) ∈ e.live G := by
    rw [hK, G.liftLive_val e y]
    exact y.2
  obtain ⟨j, hj⟩ := G.stepRot_reaches e K x hlive
  have hxy : ((G.stepFatgraph e).rot ^ j) x = y := by
    apply Subtype.ext
    rw [hj, hK, G.liftLive_val e y]
  exact ⟨(j : ℤ), by rw [zpow_natCast, hxy]⟩

theorem Fatgraph.stepFatgraph_sameVertex_of_tau {x y : ↥(e.live G)}
    (hτ : Equiv.Perm.SameCycle (e.tau G) (G.liftLive e x) (G.liftLive e y)) :
    (G.stepFatgraph e).SameVertex x y := by
  obtain ⟨K, -, hK⟩ := hτ.exists_pow_eq'
  have hlive : (↑((e.tau G ^ K) (G.liftLive e x)) : D) ∈ e.live G := by
    rw [hK, G.liftLive_val e y]
    exact y.2
  obtain ⟨j, hj⟩ := G.stepRot_reaches e K x hlive
  have hxy : ((G.stepFatgraph e).rot ^ j) x = y := by
    apply Subtype.ext
    rw [hj, hK, G.liftLive_val e y]
  exact ⟨(j : ℤ), by rw [zpow_natCast, hxy]⟩

theorem Fatgraph.stepFatgraph_sameVertex_iff {x y : ↥(e.live G)} :
    (G.stepFatgraph e).SameVertex x y ↔
      (G.SameVertex (G.liftLive e x) (G.liftLive e y)
        ∨ ((G.SameVertex (G.liftLive e x) e.a ∨ G.SameVertex (G.liftLive e x) (e.b G))
            ∧ (G.SameVertex (G.liftLive e y) e.a ∨ G.SameVertex (G.liftLive e y) (e.b G)))) := by
  constructor
  · exact G.stepFatgraph_sameVertex_elim e
  · rintro (h | ⟨hx, hy⟩)
    · exact G.stepFatgraph_sameVertex_of e h
    · have hab : Equiv.Perm.SameCycle (e.tau G) e.a (e.b G) := e.tau_sameCycle_ab G
      have hx' : Equiv.Perm.SameCycle (e.tau G) (G.liftLive e x) e.a := by
        rcases hx with h | h
        · exact e.tau_sameCycle_of_rot G h
        · exact (e.tau_sameCycle_of_rot G h).trans hab.symm
      have hy' : Equiv.Perm.SameCycle (e.tau G) (G.liftLive e y) e.a := by
        rcases hy with h | h
        · exact e.tau_sameCycle_of_rot G h
        · exact (e.tau_sameCycle_of_rot G h).trans hab.symm
      exact G.stepFatgraph_sameVertex_of_tau e (hx'.trans hy'.symm)

end MergeControl
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

structure TreeData (m : ℕ) where
  pa : Equiv.Perm (Fin m)
  pb : Equiv.Perm (Fin m)
  v₀ : Fin m
  depth : Fin m → ℕ
  parent : ∀ v : Fin m, v ≠ v₀ → Fin m × Fin 2 × Bool
  hpar : ∀ (v) (h : v ≠ v₀),
    (if (parent v h).2.2
      then (if (parent v h).2.1 = 0 then pa else pb) (parent v h).1 = v
      else (if (parent v h).2.1 = 0 then pa else pb) v = (parent v h).1)
  hdepth : ∀ (v) (h : v ≠ v₀), depth (parent v h).1 < depth v

namespace TreeData

noncomputable def repF {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) (v : Fin m) : Fin m :=
  if h : v ∈ F ∧ v ≠ T.v₀ then repF T F (T.parent v h.2).1 else v
termination_by T.depth v
decreasing_by exact T.hdepth v h.2

theorem repF_of_notMem {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) (v : Fin m)
    (hv : v ∉ F) : T.repF F v = v := by
  rw [repF]
  simp [hv]

theorem repF_root {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) : T.repF F T.v₀ = T.v₀ := by
  rw [repF]
  simp

theorem repF_mem_imp {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) (v : Fin m)
    (h : T.repF F v ∈ F) : T.repF F v = T.v₀ := by
  suffices H : ∀ n (v : Fin m), T.depth v = n → T.repF F v ∈ F → T.repF F v = T.v₀ from
    H _ v rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hvn hmem
    rw [repF] at hmem ⊢
    split_ifs at hmem ⊢ with hc
    · exact ih _ (hvn ▸ T.hdepth v hc.2) _ rfl hmem
    · by_contra hne
      exact hc ⟨hmem, hne⟩

theorem repF_depth_le {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) (v : Fin m) :
    T.depth (T.repF F v) ≤ T.depth v := by
  suffices H : ∀ n (v : Fin m), T.depth v = n → T.depth (T.repF F v) ≤ T.depth v from
    H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hvn
    rw [repF]
    split_ifs with hc
    · exact le_trans (ih _ (hvn ▸ T.hdepth v hc.2) _ rfl) (le_of_lt (T.hdepth v hc.2))
    · exact le_refl _

theorem repF_insert {m : ℕ} (T : TreeData m) (F : Finset (Fin m)) (v : Fin m)
    (hv₀ : v ≠ T.v₀) (hvF : v ∉ F) (w : Fin m) :
    T.repF (insert v F) w
      = if T.repF F w = v then T.repF F (T.parent v hv₀).1 else T.repF F w := by
  suffices H : ∀ n (w : Fin m), T.depth w = n →
      T.repF (insert v F) w
        = if T.repF F w = v then T.repF F (T.parent v hv₀).1 else T.repF F w from
    H _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hwn
    by_cases hw₀ : w = T.v₀
    · subst hw₀
      rw [T.repF_root, T.repF_root]
      rw [if_neg (Ne.symm hv₀)]
    · by_cases hwv : w = v
      · subst hwv
        have hLHS : T.repF (insert w F) w = T.repF (insert w F) (T.parent w hv₀).1 := by
          rw [repF]
          simp [hw₀]
        have hRf : T.repF F w = w := T.repF_of_notMem F w hvF
        rw [hLHS, if_pos hRf]

        have hpne : T.repF F (T.parent w hv₀).1 ≠ w := by
          intro hcon
          have h1 := T.repF_depth_le F (T.parent w hv₀).1
          rw [hcon] at h1
          exact absurd (lt_of_le_of_lt h1 (T.hdepth w hv₀)) (lt_irrefl _)
        rw [ih _ (hwn ▸ T.hdepth w hv₀) _ rfl, if_neg hpne]
      · by_cases hwF : w ∈ F
        ·
          have hmem' : w ∈ insert v F := Finset.mem_insert_of_mem hwF
          have hL : T.repF (insert v F) w = T.repF (insert v F) (T.parent w hw₀).1 := by
            rw [repF]
            simp [hmem', hw₀]
          have hR : T.repF F w = T.repF F (T.parent w hw₀).1 := by
            conv_lhs => rw [repF]
            simp [hwF, hw₀]
          rw [hL, hR, ih _ (hwn ▸ T.hdepth w hw₀) _ rfl]
        ·
          have hnm : w ∉ insert v F := by
            rw [Finset.mem_insert]
            push Not
            exact ⟨hwv, hwF⟩
          rw [T.repF_of_notMem _ w hnm, T.repF_of_notMem F w hwF, if_neg hwv]

def childDart {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) : CoverDart m :=
  (v, if (T.parent v h).2.1 = 0 then (if (T.parent v h).2.2 then 1 else 0)
      else (if (T.parent v h).2.2 then 2 else 3))

def parentDart {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) : CoverDart m :=
  coverPrtFun m T.pa T.pb (T.childDart v h)

theorem childDart_fst {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) :
    (T.childDart v h).1 = v := by
  unfold childDart
  split_ifs <;> rfl

theorem parentDart_fst {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) :
    (T.parentDart v h).1 = (T.parent v h).1 := by
  have hp := T.hpar v h
  rcases hpr : T.parent v h with ⟨p, il, dir⟩
  rw [hpr] at hp
  simp only [parentDart, childDart, coverPrtFun, hpr]
  fin_cases il <;> cases dir <;>
    simp_all [Equiv.symm_apply_eq]

theorem prt_parentDart {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) :
    coverPrtFun m T.pa T.pb (T.parentDart v h) = T.childDart v h :=
  coverPrtFun_involutive m T.pa T.pb (T.childDart v h)

theorem edgeDarts_disjoint {m : ℕ} (T : TreeData m) (u v : Fin m)
    (hu : u ≠ T.v₀) (hv : v ≠ T.v₀) (huv : u ≠ v) :
    T.childDart u hu ≠ T.childDart v hv ∧ T.childDart u hu ≠ T.parentDart v hv ∧
      T.parentDart u hu ≠ T.childDart v hv ∧ T.parentDart u hu ≠ T.parentDart v hv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcon
    exact huv (by rw [← T.childDart_fst u hu, ← T.childDart_fst v hv, hcon])
  · intro hcon
    have h1 : u = (T.parent v hv).1 := by
      rw [← T.childDart_fst u hu, hcon, T.parentDart_fst]
    have h2 : (T.parent u hu).1 = v := by
      have hc := congrArg (coverPrtFun m T.pa T.pb) hcon
      rw [T.prt_parentDart v hv] at hc
      rw [← T.parentDart_fst u hu]
      exact (congrArg Prod.fst hc).trans (T.childDart_fst v hv)
    have d1 := T.hdepth u hu
    have d2 := T.hdepth v hv
    rw [h2] at d1
    rw [← h1] at d2
    omega
  · intro hcon
    have h1 : (T.parent u hu).1 = v := by
      rw [← T.parentDart_fst u hu, hcon, T.childDart_fst]
    have h2 : u = (T.parent v hv).1 := by
      have hc := congrArg (coverPrtFun m T.pa T.pb) hcon
      rw [T.prt_parentDart u hu] at hc
      have hc2 : T.childDart u hu = T.parentDart v hv := hc
      rw [← T.childDart_fst u hu, hc2, T.parentDart_fst]
    have d1 := T.hdepth u hu
    have d2 := T.hdepth v hv
    rw [h1] at d1
    rw [← h2] at d2
    omega
  · intro hcon
    have hc := congrArg (coverPrtFun m T.pa T.pb) hcon
    rw [T.prt_parentDart u hu, T.prt_parentDart v hv] at hc
    exact huv (by rw [← T.childDart_fst u hu, hc, T.childDart_fst])

theorem exists_max_unfolded {m : ℕ} (T : TreeData m) (F : Finset (Fin m))
    (hne : ∃ w : Fin m, w ∉ F ∧ w ≠ T.v₀) :
    ∃ v : Fin m, v ∉ F ∧ v ≠ T.v₀ ∧
      ∀ w : Fin m, w ∉ F → w ≠ T.v₀ → T.depth w ≤ T.depth v := by
  classical
  obtain ⟨w, hwF, hw₀⟩ := hne
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun u => u ∉ F ∧ u ≠ T.v₀) T.depth
    ⟨w, by simp [hwF, hw₀]⟩
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.2.1, hv.2.2, fun u hu1 hu2 => hmax u (by simp [hu1, hu2])⟩

end TreeData
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

theorem ContractionSeq.snoc {D : Type*} [DecidableEq D] {s : Finset D} {G : Fatgraph s}
    {t : Finset D} {H : Fatgraph t} (C : ContractionSeq s G t H) (e : H.StepEdge) :
    ContractionSeq s G (e.live H) (H.stepFatgraph e) := by
  induction C with
  | nil s G => exact .cons s G e _ _ (.nil _ _)
  | cons s G e₀ t H htail ih => exact .cons s G e₀ _ _ (ih e)

theorem TreeData.childDart_ne_parentDart {m : ℕ} (T : TreeData m) (v : Fin m) (h : v ≠ T.v₀) :
    T.childDart v h ≠ T.parentDart v h := by
  intro hcon
  have h1 := congrArg Prod.fst hcon
  rw [T.childDart_fst, T.parentDart_fst] at h1
  have h2 := T.hdepth v h
  rw [← h1] at h2
  exact lt_irrefl _ h2

theorem TreeData.fold_stage {m : ℕ} (T : TreeData m) (F : Finset (Fin m))
    (hroot : T.v₀ ∉ F)
    (hmax : ∀ u ∈ F, ∀ w : Fin m, w ∉ F → w ≠ T.v₀ → T.depth w ≤ T.depth u) :
    ∃ (t : Finset (CoverDart m)) (H : Fatgraph t)
      (_C : ContractionSeq Finset.univ (coverFatgraph m T.pa T.pb) t H),
      (∀ x : ↥t, (↑(H.prt x) : CoverDart m) = coverPrtFun m T.pa T.pb ↑x) ∧
      (∀ d : CoverDart m, d ∈ t ↔ ∀ (w : Fin m) (hw : w ≠ T.v₀), w ∈ F →
          d ≠ T.childDart w hw ∧ d ≠ T.parentDart w hw) ∧
      t.card = 4 * m - 2 * F.card ∧
      (∀ d f : ↥t, H.SameVertex d f ↔ T.repF F d.1.1 = T.repF F f.1.1) := by
  classical
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    rcases Finset.eq_empty_or_nonempty F with rfl | hFne
    · refine ⟨Finset.univ, coverFatgraph m T.pa T.pb, ContractionSeq.nil _ _,
        fun x => rfl, ?_, ?_, ?_⟩
      · intro d
        simp
      · rw [Finset.card_univ]
        simp only [Finset.card_empty] at hn
        simp only [Fintype.card_prod, Fintype.card_fin]
        omega
      · intro d f
        rw [coverFatgraph_sameVertex_iff,
          T.repF_of_notMem ∅ _ (Finset.notMem_empty _),
          T.repF_of_notMem ∅ _ (Finset.notMem_empty _)]
    · obtain ⟨v, hvF, hvmin⟩ := F.exists_min_image T.depth hFne
      have hv₀ : v ≠ T.v₀ := fun h => hroot (h ▸ hvF)
      have hvF' : v ∉ F.erase v := Finset.notMem_erase v F
      have hcard' : (F.erase v).card < n := hn ▸ Finset.card_erase_lt_of_mem hvF
      have hroot' : T.v₀ ∉ F.erase v := fun h => hroot (Finset.mem_of_mem_erase h)
      have hmax' : ∀ u ∈ F.erase v, ∀ w : Fin m, w ∉ F.erase v → w ≠ T.v₀ →
          T.depth w ≤ T.depth u := by
        intro u hu w hwF' hw₀
        by_cases hwF : w ∈ F
        · have hwv : w = v := by
            by_contra hne
            exact hwF' (Finset.mem_erase.mpr ⟨hne, hwF⟩)
          subst hwv
          exact hvmin u (Finset.mem_of_mem_erase hu)
        · exact hmax u (Finset.mem_of_mem_erase hu) w hwF hw₀
      obtain ⟨t', H', C', hprt', hmem', hcard'', hcls'⟩ :=
        ih (F.erase v).card hcard' (F.erase v) hroot' hmax' rfl
      have hpF : (T.parent v hv₀).1 ∉ F := by
        intro hpFmem
        have h1 := hvmin _ hpFmem
        have h2 := T.hdepth v hv₀
        omega
      have hpF' : (T.parent v hv₀).1 ∉ F.erase v := fun h => hpF (Finset.mem_of_mem_erase h)
      have hpv_ne : (T.parent v hv₀).1 ≠ v := by
        intro h
        have := T.hdepth v hv₀
        rw [h] at this
        exact lt_irrefl _ this

      have hsurv : ∀ d : CoverDart m,
          (d = T.childDart v hv₀ ∨ d = T.parentDart v hv₀) → d ∈ t' := by
        intro d hd
        rw [hmem']
        intro w hw hwF'
        have hwv : w ≠ v := fun h => hvF' (h ▸ hwF')
        have hdisj := T.edgeDarts_disjoint w v hw hv₀ hwv
        rcases hd with rfl | rfl
        · exact ⟨Ne.symm hdisj.1, Ne.symm hdisj.2.2.1⟩
        · exact ⟨Ne.symm hdisj.2.1, Ne.symm hdisj.2.2.2⟩
      have hcd : T.childDart v hv₀ ∈ t' := hsurv _ (Or.inl rfl)
      have hpd : T.parentDart v hv₀ ∈ t' := hsurv _ (Or.inr rfl)

      have hbval : (↑(H'.prt ⟨T.childDart v hv₀, hcd⟩) : CoverDart m) = T.parentDart v hv₀ :=
        hprt' ⟨T.childDart v hv₀, hcd⟩
      have hcross : ¬ H'.SameVertex ⟨T.childDart v hv₀, hcd⟩ (H'.prt ⟨T.childDart v hv₀, hcd⟩) := by
        rw [hcls']
        simp only [T.childDart_fst]
        have hb1 : (H'.prt ⟨T.childDart v hv₀, hcd⟩).1.1 = (T.parent v hv₀).1 := by
          rw [hbval]
          exact T.parentDart_fst v hv₀
        rw [hb1, T.repF_of_notMem _ _ hvF', T.repF_of_notMem _ _ hpF']
        exact fun h => hpv_ne h.symm
      set e : H'.StepEdge := ⟨⟨T.childDart v hv₀, hcd⟩, hcross⟩ with he
      have heaval : (↑(e.a) : CoverDart m) = T.childDart v hv₀ := rfl
      have hebval : (↑(e.b H') : CoverDart m) = T.parentDart v hv₀ := hbval
      have hprtd₀ : (↑(H'.prt e.d₀) : CoverDart m) = T.parentDart v hv₀ := hbval
      refine ⟨e.live H', H'.stepFatgraph e, C'.snoc e, ?_, ?_, ?_, ?_⟩
      ·
        intro x
        have : (↑((H'.stepFatgraph e).prt x) : CoverDart m)
            = ↑(H'.prt ⟨↑x, ((e.mem_live H' ↑x).mp x.2).1⟩) := rfl
        rw [this, hprt']
      ·
        intro d
        rw [e.mem_live, hmem', heaval, hebval]
        constructor
        · rintro ⟨hall, hne1, hne2⟩ w hw hwF
          by_cases hwv : w = v
          · subst hwv
            exact ⟨hne1, hne2⟩
          · exact hall w hw (Finset.mem_erase.mpr ⟨hwv, hwF⟩)
        · intro hall
          refine ⟨fun w hw hwF' => hall w hw (Finset.mem_of_mem_erase hwF'), ?_, ?_⟩
          · exact (hall v hv₀ hvF).1
          · exact (hall v hv₀ hvF).2
      ·
        have hlive : e.live H' = (t'.erase (T.childDart v hv₀)).erase (T.parentDart v hv₀) := by
          unfold Fatgraph.StepEdge.live
          rw [show (↑(e.a) : CoverDart m) = T.childDart v hv₀ from rfl]
          rw [hprtd₀]
        have hpdmem : T.parentDart v hv₀ ∈ t'.erase (T.childDart v hv₀) :=
          Finset.mem_erase.mpr ⟨Ne.symm (T.childDart_ne_parentDart v hv₀), hpd⟩
        rw [hlive, Finset.card_erase_of_mem hpdmem, Finset.card_erase_of_mem hcd, hcard'']
        have herase : (F.erase v).card = F.card - 1 := Finset.card_erase_of_mem hvF
        have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨v, hvF⟩
        have ht2 : 2 ≤ t'.card := by
          have := Finset.one_lt_card.mpr
            ⟨T.childDart v hv₀, hcd, T.parentDart v hv₀, hpd,
              T.childDart_ne_parentDart v hv₀⟩
          omega
        omega
      ·
        intro x y
        rw [H'.stepFatgraph_sameVertex_iff e, hcls', hcls', hcls', hcls', hcls']
        have hxv : (H'.liftLive e x).1.1 = x.1.1 := by
          rw [show ((H'.liftLive e x) : CoverDart m) = ↑x from H'.liftLive_val e x]
        have hyv : (H'.liftLive e y).1.1 = y.1.1 := by
          rw [show ((H'.liftLive e y) : CoverDart m) = ↑y from H'.liftLive_val e y]
        have hav : (e.a).1.1 = v := by
          rw [show (↑(e.a) : CoverDart m) = T.childDart v hv₀ from rfl, T.childDart_fst]
        have hbv : (e.b H').1.1 = (T.parent v hv₀).1 := by
          rw [show (↑(e.b H') : CoverDart m) = T.parentDart v hv₀ from hebval, T.parentDart_fst]
        rw [hxv, hyv, hav, hbv,
          T.repF_of_notMem _ _ hvF', T.repF_of_notMem _ _ hpF']
        have hFins : F = insert v (F.erase v) := (Finset.insert_erase hvF).symm
        rw [show T.repF F x.1.1 = T.repF (insert v (F.erase v)) x.1.1 from by rw [← hFins],
          show T.repF F y.1.1 = T.repF (insert v (F.erase v)) y.1.1 from by rw [← hFins],
          T.repF_insert _ v hv₀ hvF', T.repF_insert _ v hv₀ hvF',
          T.repF_of_notMem _ _ hpF']
        set rx := T.repF (F.erase v) x.1.1
        set ry := T.repF (F.erase v) y.1.1
        by_cases h1 : rx = v <;> by_cases h2 : ry = v
        · rw [if_pos h1, if_pos h2]
          exact iff_of_true (Or.inl (h1.trans h2.symm)) rfl
        · rw [if_pos h1, if_neg h2]
          constructor
          · rintro (h | ⟨-, hb | hb⟩)
            · exact absurd (h.symm.trans h1) h2
            · exact absurd hb h2
            · exact hb.symm
          · intro h
            exact Or.inr ⟨Or.inl h1, Or.inr h.symm⟩
        · rw [if_neg h1, if_pos h2]
          constructor
          · rintro (h | ⟨ha | ha, -⟩)
            · exact absurd (h.trans h2) h1
            · exact absurd ha h1
            · exact ha
          · intro h
            exact Or.inr ⟨Or.inr h, Or.inl h2⟩
        · rw [if_neg h1, if_neg h2]
          constructor
          · rintro (h | ⟨ha | ha, hb | hb⟩)
            · exact h
            · exact absurd ha h1
            · exact absurd ha h1
            · exact absurd hb h2
            · exact ha.trans hb.symm
          · exact Or.inl

theorem TreeData.exists_contraction {m : ℕ} (hm : 0 < m) (T : TreeData m) :
    ∃ (t : Finset (CoverDart m)) (H : Fatgraph t)
      (_C : ContractionSeq Finset.univ (coverFatgraph m T.pa T.pb) t H),
      t.card = 2 * (m + 1) ∧
      (∀ x : ↥t, (↑(H.prt x) : CoverDart m) = coverPrtFun m T.pa T.pb ↑x) ∧
      (∀ d : CoverDart m, d ∈ t ↔ ∀ (w : Fin m) (hw : w ≠ T.v₀),
          d ≠ T.childDart w hw ∧ d ≠ T.parentDart w hw) ∧
      (∀ d f : ↥t, H.SameVertex d f) := by
  classical
  set F : Finset (Fin m) := Finset.univ.erase T.v₀ with hF
  have hroot : T.v₀ ∉ F := Finset.notMem_erase _ _
  have hmax : ∀ u ∈ F, ∀ w : Fin m, w ∉ F → w ≠ T.v₀ → T.depth w ≤ T.depth u := by
    intro u hu w hwF hw₀
    exact absurd (Finset.mem_erase.mpr ⟨hw₀, Finset.mem_univ w⟩) hwF
  obtain ⟨t, H, C, hprt, hmem, hcard, hcls⟩ := T.fold_stage F hroot hmax
  have hFcard : F.card = m - 1 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hrep : ∀ z : Fin m, T.repF F z = T.v₀ := by
    intro z
    by_cases hz : T.repF F z ∈ F
    · exact T.repF_mem_imp F z hz
    · by_contra hne
      exact hz (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
  refine ⟨t, H, C, ?_, hprt, ?_, ?_⟩
  · rw [hcard, hFcard]
    omega
  · intro d
    rw [hmem]
    constructor
    · intro hall w hw
      exact hall w hw (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)
    · intro hall w hw _
      exact hall w hw
  · intro d f
    rw [hcls, hrep, hrep]

theorem TreeData.face_meets {m : ℕ} (T : TreeData m) (t : Finset (CoverDart m))
    (hmem : ∀ d : CoverDart m, d ∈ t ↔ ∀ (w : Fin m) (hw : w ≠ T.v₀),
        d ≠ T.childDart w hw ∧ d ≠ T.parentDart w hw)
    (x : ↥(Finset.univ : Finset (CoverDart m))) :
    ∃ k : ℕ, (↑(((coverFatgraph m T.pa T.pb).facePerm ^ k) x) : CoverDart m) ∈ t := by
  classical
  by_contra hcon
  push Not at hcon
  set fp := (coverFatgraph m T.pa T.pb).facePerm with hfp
  have hslot : ∀ sl : Fin 4, (finRotate 4).symm sl ≠ sl := by decide
  have hclass : ∀ j : ℕ, ∃ (w : Fin m) (hw : w ≠ T.v₀),
      (↑((fp ^ j) x) : CoverDart m) = T.childDart w hw
        ∨ (↑((fp ^ j) x) : CoverDart m) = T.parentDart w hw := by
    intro j
    have hj := hcon j
    rw [hmem] at hj
    obtain ⟨w, hw2⟩ := not_forall.mp hj
    obtain ⟨hw, hrest⟩ := not_forall.mp hw2
    rcases not_and_or.mp hrest with hc | hc
    · exact ⟨w, hw, Or.inl (not_not.mp hc)⟩
    · exact ⟨w, hw, Or.inr (not_not.mp hc)⟩
  have hper : x ∈ Function.periodicPts ⇑fp := by
    refine ⟨orderOf fp, orderOf_pos _, ?_⟩
    show Function.IsPeriodicPt _ _ _
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Fatgraph.perm_pow_apply', pow_orderOf_eq_one]
    rfl
  set P := Function.minimalPeriod (⇑fp) x with hP
  have hmpos : 0 < P := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hmod : ∀ j : ℕ, (fp ^ (j % P)) x = (fp ^ j) x := by
    intro j
    rw [Fatgraph.perm_pow_apply', Fatgraph.perm_pow_apply', hP, Function.iterate_mod_minimalPeriod_eq]
  obtain ⟨K, hKmem, hKmax⟩ := (Finset.range P).exists_max_image
    (fun j => T.depth ((↑((fp ^ j) x) : CoverDart m).1)) ⟨0, Finset.mem_range.mpr hmpos⟩
  have hmaxall : ∀ j : ℕ, T.depth ((↑((fp ^ j) x) : CoverDart m).1)
      ≤ T.depth ((↑((fp ^ K) x) : CoverDart m).1) := by
    intro j
    have h := hKmax (j % P) (Finset.mem_range.mpr (Nat.mod_lt _ hmpos))
    rw [hmod j] at h
    exact h
  have hstep : ∀ d : ↥(Finset.univ : Finset (CoverDart m)),
      (↑(fp d) : CoverDart m).1
        = (↑((coverFatgraph m T.pa T.pb).prt d) : CoverDart m).1 := fun _ => rfl
  have hprtval : ∀ d : ↥(Finset.univ : Finset (CoverDart m)),
      (↑((coverFatgraph m T.pa T.pb).prt d) : CoverDart m)
        = coverPrtFun m T.pa T.pb ↑d := fun _ => rfl
  have hfpval : ∀ d : ↥(Finset.univ : Finset (CoverDart m)),
      (↑(fp d) : CoverDart m)
        = ((↑((coverFatgraph m T.pa T.pb).prt d) : CoverDart m).1,
            (finRotate 4).symm (↑((coverFatgraph m T.pa T.pb).prt d) : CoverDart m).2) :=
    fun _ => rfl
  obtain ⟨w, hw, hKclass⟩ := hclass K

  have hKchild : (↑((fp ^ K) x) : CoverDart m) = T.childDart w hw := by
    rcases hKclass with h | h
    · exact h
    · exfalso
      have h1 : (↑((fp ^ (K + 1)) x) : CoverDart m).1 = w := by
        rw [pow_succ', Equiv.Perm.mul_apply, hstep, hprtval, h, T.prt_parentDart,
          T.childDart_fst]
      have h2 := hmaxall (K + 1)
      rw [h1] at h2
      have h3 : T.depth ((↑((fp ^ K) x) : CoverDart m).1) < T.depth w := by
        rw [h, T.parentDart_fst]
        exact T.hdepth w hw
      omega

  have hcycP : (fp ^ P) x = x := by
    rw [Fatgraph.perm_pow_apply', hP, Function.iterate_minimalPeriod]
  have hKP : K + P - 1 + 1 = K + P := by omega
  have hprev : fp ((fp ^ (K + P - 1)) x) = (fp ^ K) x := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ', hKP, pow_add, Equiv.Perm.mul_apply, hcycP]
  obtain ⟨w', hw', hprevclass⟩ := hclass (K + P - 1)
  rcases hprevclass with hcase' | hcase'
  ·
    have h1 : (↑(fp ((fp ^ (K + P - 1)) x)) : CoverDart m).1 = (T.parent w' hw').1 := by
      rw [hstep, hprtval, hcase']
      exact T.parentDart_fst w' hw'
    rw [hprev, hKchild, T.childDart_fst] at h1
    have h2 := hmaxall (K + P - 1)
    rw [hcase', T.childDart_fst, hKchild, T.childDart_fst] at h2
    have h3 := T.hdepth w' hw'
    rw [← h1] at h3
    omega
  ·
    have hpr : (↑((coverFatgraph m T.pa T.pb).prt ((fp ^ (K + P - 1)) x)) : CoverDart m)
        = T.childDart w' hw' := by
      rw [hprtval, hcase', T.prt_parentDart]
    have hv : w = w' := by
      have h1 : (↑(fp ((fp ^ (K + P - 1)) x)) : CoverDart m).1 = w' := by
        rw [hstep, hpr, T.childDart_fst]
      rw [hprev, hKchild, T.childDart_fst] at h1
      exact h1
    subst hv
    have hval : (↑(fp ((fp ^ (K + P - 1)) x)) : CoverDart m)
        = ((T.childDart w hw').1, (finRotate 4).symm (T.childDart w hw').2) := by
      rw [hfpval, hpr]
    rw [hprev, hKchild] at hval
    have hsnd := congrArg Prod.snd hval
    exact hslot (T.childDart w hw').2 (by
      have hpi : (T.childDart w hw).2 = (T.childDart w hw').2 := rfl
      rw [hpi] at hsnd
      exact hsnd.symm)

end PDPairing.Cover
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

section prints
set_option pp.deepTerms true
set_option pp.proofs true
end prints
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

namespace PDPairing
namespace Cover

section PipeExports

variable {D : Type*} [DecidableEq D]

section E3GenStep

variable {M : Type*} [AddCommMonoid M]
variable {t : Finset D} (H : Fatgraph t) (e : H.StepEdge)

theorem Fatgraph.sigmaIdx_sum_gen (x : ↥(e.live H)) (gH : ℕ → M)
    (hmid : ∀ k r, 0 < r → r < H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) →
      gH (H.sigmaIdx e x k + r) = 0)
    (j : ℕ) :
    (∑ i ∈ Finset.range (H.sigmaIdx e x j), gH i)
      = ∑ k ∈ Finset.range j, gH (H.sigmaIdx e x k) := by
  induction j with
  | zero =>
    rw [H.sigmaIdx_zero e x]
    simp
  | succ k ih =>
    have hL13 : H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 1
        ∨ H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 2
        ∨ H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) = 3 := by
      have h1 := H.stepLen_pos' e x k
      have h2 := H.stepLen_le e (((H.stepFatgraph e).facePerm ^ k) x)
      omega
    rw [H.sigmaIdx_succ e x k, Finset.sum_range_succ]
    rcases hL13 with hL | hL | hL
    · rw [hL, Finset.sum_range_succ, ih]
    · rw [hL, show H.sigmaIdx e x k + 2 = (H.sigmaIdx e x k + 1) + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        hmid k 1 (by omega) (by omega), add_zero]
    · rw [hL, show H.sigmaIdx e x k + 3 = ((H.sigmaIdx e x k + 1) + 1) + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        hmid k 1 (by omega) (by omega), hmid k 2 (by omega) (by omega), add_zero, add_zero]

theorem Fatgraph.sigmaIdx_sum_gen_midH (x : ↥(e.live H)) (g : D → M)
    (hga : g ↑e.a = 0) (hgb : g ↑(e.b H) = 0) :
    ∀ k r, 0 < r → r < H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) →
      g ↑((H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x)) = 0 := by
  have hgdel : ∀ z : ↥t, (↑z : D) ∉ e.live H → g ↑z = 0 := by
    intro z hz
    rcases H.eq_deleted_of_not_live e z hz with h | h
    · rw [h, hga]
    · rw [h, hgb]
  intro k r hr1 hr2
  have hpos : (H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x)
      = (H.facePerm ^ r) (H.liftLive e (((H.stepFatgraph e).facePerm ^ k) x)) := by
    rw [add_comm, pow_add]
    show (H.facePerm ^ r) ((H.facePerm ^ H.sigmaIdx e x k) (H.liftLive e x)) = _
    rw [H.sigmaIdx_spec e x k]
  rw [hpos]
  exact hgdel _ ((H.stepLen_spec e (((H.stepFatgraph e).facePerm ^ k) x)).2 r hr1 hr2)

theorem Fatgraph.sigmaIdx_sum' (x : ↥(e.live H)) (g : D → M)
    (hga : g ↑e.a = 0) (hgb : g ↑(e.b H) = 0) (j : ℕ) :
    (∑ i ∈ Finset.range (H.sigmaIdx e x j), g ↑((H.facePerm ^ i) (H.liftLive e x)))
      = ∑ k ∈ Finset.range j, g ↑(((H.stepFatgraph e).facePerm ^ k) x) := by
  have hhead : ∀ k : ℕ, g ↑((H.facePerm ^ (H.sigmaIdx e x k)) (H.liftLive e x))
      = g ↑(((H.stepFatgraph e).facePerm ^ k) x) := by
    intro k
    rw [H.sigmaIdx_spec e x k, H.liftLive_val]
  have key := H.sigmaIdx_sum_gen e x (fun i => g ↑((H.facePerm ^ i) (H.liftLive e x)))
    (H.sigmaIdx_sum_gen_midH e x g hga hgb) j
  rw [key]
  exact Finset.sum_congr rfl fun k _ => hhead k

end E3GenStep
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

section E3GenPipe

variable {M : Type*} [AddCommMonoid M]

theorem Fatgraph.step_orbit_sum_gen {t : Finset D} (H : Fatgraph t) (e : H.StepEdge) (g : D → M)
    (hga : g ↑e.a = 0) (hgb : g ↑(e.b H) = 0) (x : ↥(e.live H)) :
    (∑ k ∈ Finset.range (Function.minimalPeriod
        (⇑(H.stepFatgraph e).facePerm) x),
      g ↑(((H.stepFatgraph e).facePerm ^ k) x))
    = ∑ k ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)),
      g ↑((H.facePerm ^ k) (H.liftLive e x)) := by
  rw [H.sigmaIdx_minPer e x]
  exact (H.sigmaIdx_sum' e x g hga hgb _).symm

theorem Fatgraph.pipe_orbit_sum_gen {s₀ : Finset D} (G₀ : Fatgraph s₀) {t : Finset D}
    {H : Fatgraph t} (C : ContractionSeq s₀ G₀ t H) :
    ∀ (g : D → M), (∀ d ∈ s₀, d ∉ t → g d = 0) →
    ∀ x : ↥t,
      (∑ k ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) x),
        g ↑((H.facePerm ^ k) x))
      = ∑ k ∈ Finset.range (Function.minimalPeriod (⇑G₀.facePerm)
          ⟨↑x, C.live_subset x.2⟩),
        g ↑((G₀.facePerm ^ k) ⟨↑x, C.live_subset x.2⟩) := by
  induction C with
  | nil s G =>
    intro g hg x
    rfl
  | cons s G e t' H' htail ih =>
    intro g hg x
    have hanotlive : (↑e.a : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑e.a).mp hmem).2.1 rfl
    have hbnotlive : (↑(e.b G) : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑(e.b G)).mp hmem).2.2 rfl
    have hga : g ↑e.a = 0 :=
      hg ↑e.a (Finset.coe_mem _) (fun ht' => hanotlive (htail.live_subset ht'))
    have hgb : g ↑(e.b G) = 0 :=
      hg ↑(e.b G) (Finset.coe_mem _) (fun ht' => hbnotlive (htail.live_subset ht'))
    have hg' : ∀ d ∈ e.live G, d ∉ t' → g d = 0 := fun d hd hnt =>
      hg d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hnt
    have h1 := ih g hg' x
    have h2 := G.step_orbit_sum_gen e g hga hgb ⟨↑x, htail.live_subset x.2⟩
    exact h1.trans h2

theorem Fatgraph.step_orbit_pairSum {t : Finset D} (H : Fatgraph t) (e : H.StepEdge) (F : D → D → M)
    (hFaL : ∀ d, F ↑e.a d = 0) (hFbL : ∀ d, F ↑(e.b H) d = 0)
    (hFaR : ∀ d, F d ↑e.a = 0) (hFbR : ∀ d, F d ↑(e.b H) = 0) (x : ↥(e.live H)) :
    (∑ b ∈ Finset.range (Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x),
      ∑ a ∈ Finset.range b,
        F ↑(((H.stepFatgraph e).facePerm ^ a) x) ↑(((H.stepFatgraph e).facePerm ^ b) x))
    = ∑ i₂ ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) (H.liftLive e x)),
      ∑ i₁ ∈ Finset.range i₂,
        F ↑((H.facePerm ^ i₁) (H.liftLive e x)) ↑((H.facePerm ^ i₂) (H.liftLive e x)) := by
  set M' := Function.minimalPeriod (⇑(H.stepFatgraph e).facePerm) x with hM'

  rw [H.sigmaIdx_minPer e x]
  have hmidO : ∀ k r, 0 < r → r < H.stepLen e (((H.stepFatgraph e).facePerm ^ k) x) →
      (∑ i₁ ∈ Finset.range (H.sigmaIdx e x k + r),
        F ↑((H.facePerm ^ i₁) (H.liftLive e x))
          ↑((H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x))) = 0 := by
    intro k r hr1 hr2

    have hpos : (H.facePerm ^ (H.sigmaIdx e x k + r)) (H.liftLive e x)
        = (H.facePerm ^ r) (H.liftLive e (((H.stepFatgraph e).facePerm ^ k) x)) := by
      rw [add_comm, pow_add]
      show (H.facePerm ^ r) ((H.facePerm ^ H.sigmaIdx e x k) (H.liftLive e x)) = _
      rw [H.sigmaIdx_spec e x k]
    have hnotlive := (H.stepLen_spec e (((H.stepFatgraph e).facePerm ^ k) x)).2 r hr1 hr2
    rcases H.eq_deleted_of_not_live e _ hnotlive with hD | hD
    · apply Finset.sum_eq_zero; intro i₁ _; rw [hpos, hD]; exact hFaR _
    · apply Finset.sum_eq_zero; intro i₁ _; rw [hpos, hD]; exact hFbR _
  have hOuter := H.sigmaIdx_sum_gen e x
    (fun i₂ => ∑ i₁ ∈ Finset.range i₂,
      F ↑((H.facePerm ^ i₁) (H.liftLive e x)) ↑((H.facePerm ^ i₂) (H.liftLive e x)))
    hmidO M'
  rw [hOuter]

  refine Finset.sum_congr rfl fun β _ => ?_

  have hdβ : (↑((H.facePerm ^ (H.sigmaIdx e x β)) (H.liftLive e x)) : D)
      = ↑(((H.stepFatgraph e).facePerm ^ β) x) := by
    rw [H.sigmaIdx_spec e x β, H.liftLive_val]
  rw [hdβ]

  exact (H.sigmaIdx_sum' e x (fun d => F d ↑(((H.stepFatgraph e).facePerm ^ β) x))
    (hFaL _) (hFbL _) β).symm

theorem Fatgraph.pipe_orbit_pairSum {s₀ : Finset D} (G₀ : Fatgraph s₀) {t : Finset D}
    {H : Fatgraph t} (C : ContractionSeq s₀ G₀ t H) :
    ∀ (F : D → D → M),
    (∀ d ∈ s₀, d ∉ t → (∀ d', F d d' = 0) ∧ (∀ d', F d' d = 0)) →
    ∀ x : ↥t,
      (∑ b ∈ Finset.range (Function.minimalPeriod (⇑H.facePerm) x),
        ∑ a ∈ Finset.range b, F ↑((H.facePerm ^ a) x) ↑((H.facePerm ^ b) x))
      = ∑ i₂ ∈ Finset.range (Function.minimalPeriod (⇑G₀.facePerm) ⟨↑x, C.live_subset x.2⟩),
        ∑ i₁ ∈ Finset.range i₂,
          F ↑((G₀.facePerm ^ i₁) ⟨↑x, C.live_subset x.2⟩)
            ↑((G₀.facePerm ^ i₂) ⟨↑x, C.live_subset x.2⟩) := by
  induction C with
  | nil s G =>
    intro F hF x
    rfl
  | cons s G e t' H' htail ih =>
    intro F hF x
    have hanotlive : (↑e.a : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑e.a).mp hmem).2.1 rfl
    have hbnotlive : (↑(e.b G) : D) ∉ e.live G := by
      intro hmem
      exact ((e.mem_live G ↑(e.b G)).mp hmem).2.2 rfl
    have haDel := hF ↑e.a (Finset.coe_mem _) (fun ht' => hanotlive (htail.live_subset ht'))
    have hbDel := hF ↑(e.b G) (Finset.coe_mem _) (fun ht' => hbnotlive (htail.live_subset ht'))
    have hF' : ∀ d ∈ e.live G, d ∉ t' → (∀ d', F d d' = 0) ∧ (∀ d', F d' d = 0) :=
      fun d hd hnt => hF d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hnt
    have h1 := ih F hF' x
    have h2 := G.step_orbit_pairSum e F haDel.1 hbDel.1 haDel.2 hbDel.2
      ⟨↑x, htail.live_subset x.2⟩
    exact h1.trans h2

end E3GenPipe
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

end PipeExports
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

end PDPairing.Cover
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover"

set_option autoImplicit false

open scoped MatrixGroups

section InlinedSAN123

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace Sanov
p2m_open "ModularCurve"

def sanovA : SL(2, ℤ) := ModularGroup.T ^ 2

def sanovB : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem coe_sanovA : (↑sanovA : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2; 0, 1] := by
  have h := ModularGroup.coe_T_zpow (2 : ℤ)
  rw [zpow_two] at h
  simpa [sanovA, sq] using h

@[scoped simp] theorem coe_sanovB : (↑sanovB : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := rfl

def sanovSubgroup : Subgroup SL(2, ℤ) := Subgroup.closure {sanovA, sanovB}

open scoped Pointwise

example : DistribMulAction SL(2, ℤ) (Fin 2 → ℤ) := inferInstance

theorem smul_apply_0 (m : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (m • v) 0 = (m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 + (m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1 := by
  show ((m : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem smul_apply_1 (m : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (m • v) 1 = (m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 + (m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1 := by
  show ((m : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem coe_sanovA_zpow (n : ℤ) :
    (↑(sanovA ^ n) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2 * n; 0, 1] := by
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, SpecialLinearGroup.coe_mul, ih, coe_sanovA]
    simp only [Matrix.mul_fin_two]; ring_nf
  | pred k ih =>
    rw [zpow_sub_one, SpecialLinearGroup.coe_mul, ih]
    have hAinv : (↑(sanovA⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -2; 0, 1] := by
      rw [SpecialLinearGroup.coe_inv, coe_sanovA, Matrix.adjugate_fin_two]; simp
    rw [hAinv]
    simp only [Matrix.mul_fin_two]; ring_nf

theorem coe_sanovB_zpow (n : ℤ) :
    (↑(sanovB ^ n) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2 * n, 1] := by
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, SpecialLinearGroup.coe_mul, ih, coe_sanovB]
    simp only [Matrix.mul_fin_two]; ring_nf
  | pred k ih =>
    rw [zpow_sub_one, SpecialLinearGroup.coe_mul, ih]
    have hBinv : (↑(sanovB⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -2, 1] := by
      rw [SpecialLinearGroup.coe_inv, coe_sanovB, Matrix.adjugate_fin_two]; simp
    rw [hBinv]
    simp only [Matrix.mul_fin_two]; ring_nf

theorem sanovA_zpow_smul (n : ℤ) (v : Fin 2 → ℤ) :
    (sanovA ^ n • v) 0 = v 0 + 2 * n * v 1 ∧ (sanovA ^ n • v) 1 = v 1 := by
  refine ⟨?_, ?_⟩
  · rw [smul_apply_0, coe_sanovA_zpow]; simp
  · rw [smul_apply_1, coe_sanovA_zpow]; simp

theorem sanovB_zpow_smul (n : ℤ) (v : Fin 2 → ℤ) :
    (sanovB ^ n • v) 0 = v 0 ∧ (sanovB ^ n • v) 1 = 2 * n * v 0 + v 1 := by
  refine ⟨?_, ?_⟩
  · rw [smul_apply_0, coe_sanovB_zpow]; simp
  · rw [smul_apply_1, coe_sanovB_zpow]; simp

def sanovP : Set (Fin 2 → ℤ) := {v | |v 1| < |v 0|}

def sanovQ : Set (Fin 2 → ℤ) := {v | |v 0| < |v 1|}

theorem sanovP_nonempty : sanovP.Nonempty := ⟨![1, 0], by simp [sanovP]⟩
theorem sanovQ_nonempty : sanovQ.Nonempty := ⟨![0, 1], by simp [sanovQ]⟩

theorem disjoint_sanovP_sanovQ : Disjoint sanovP sanovQ := by
  rw [Set.disjoint_left]
  intro v hP hQ
  simp only [sanovP, sanovQ, Set.mem_setOf_eq] at hP hQ
  exact absurd (lt_trans hQ hP) (lt_irrefl _)

theorem sanovA_zpow_smul_sanovQ_subset (n : ℤ) (hn : n ≠ 0) :
    sanovA ^ n • sanovQ ⊆ sanovP := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [sanovQ, Set.mem_setOf_eq] at hv
  simp only [sanovP, Set.mem_setOf_eq, (sanovA_zpow_smul n v).1, (sanovA_zpow_smul n v).2]
  have h1n : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
  have habs : |2 * n * v 1| = 2 * |n| * |v 1| := by
    rw [abs_mul, abs_mul]; norm_num
  have key : |2 * n * v 1| ≤ |v 0 + 2 * n * v 1| + |v 0| := by
    have h := abs_add_le (v 0 + 2 * n * v 1) (-(v 0))
    rw [show v 0 + 2 * n * v 1 + -v 0 = 2 * n * v 1 by ring, abs_neg] at h
    exact h
  calc |v 1| < 2 * |v 1| - |v 0| := by linarith
    _ ≤ 2 * |n| * |v 1| - |v 0| := by nlinarith [abs_nonneg (v 1)]
    _ = |2 * n * v 1| - |v 0| := by rw [habs]
    _ ≤ |v 0 + 2 * n * v 1| := by linarith

theorem sanovB_zpow_smul_sanovP_subset (n : ℤ) (hn : n ≠ 0) :
    sanovB ^ n • sanovP ⊆ sanovQ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [sanovP, Set.mem_setOf_eq] at hv
  simp only [sanovQ, Set.mem_setOf_eq, (sanovB_zpow_smul n v).1, (sanovB_zpow_smul n v).2]
  have h1n : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
  have habs : |2 * n * v 0| = 2 * |n| * |v 0| := by
    rw [abs_mul, abs_mul]; norm_num
  have key : |2 * n * v 0| ≤ |2 * n * v 0 + v 1| + |v 1| := by
    have h := abs_add_le (2 * n * v 0 + v 1) (-(v 1))
    rw [show 2 * n * v 0 + v 1 + -v 1 = 2 * n * v 0 by ring, abs_neg] at h
    exact h
  calc |v 0| < 2 * |v 0| - |v 1| := by linarith
    _ ≤ 2 * |n| * |v 0| - |v 1| := by nlinarith [abs_nonneg (v 0)]
    _ = |2 * n * v 0| - |v 1| := by rw [habs]
    _ ≤ |2 * n * v 0 + v 1| := by linarith

def sanovFactor (i : Fin 2) : FreeGroup Unit →* SL(2, ℤ) :=
  FreeGroup.lift fun _ => ![sanovA, sanovB] i

def sanovLift : Monoid.CoprodI (fun _ : Fin 2 => FreeGroup Unit) →* SL(2, ℤ) :=
  Monoid.CoprodI.lift sanovFactor

open Monoid in

theorem sanovLift_injective : Function.Injective sanovLift := by
  apply CoprodI.lift_injective_of_ping_pong sanovFactor ?_
    (![sanovP, sanovQ]) ?_ ?_ ?_
  ·
    right
    haveI : Infinite (FreeGroup Unit) :=
      FreeGroup.freeGroupUnitEquivInt.infinite_iff.mpr inferInstance
    refine ⟨0, le_trans ?_ (Cardinal.aleph0_le_mk _)⟩
    exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3)).le
  ·
    intro i; fin_cases i
    · exact sanovP_nonempty
    · exact sanovQ_nonempty
  ·
    intro i j hij; fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_sanovP_sanovQ
    · exact disjoint_sanovP_sanovQ.symm
    · exact absurd rfl hij
  ·
    intro i j hij h hh
    set n := FreeGroup.freeGroupUnitEquivInt h with hndef
    have hheq : h = FreeGroup.of () ^ n := by
      have := FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h
      rw [← hndef] at this
      exact this.symm
    have hn : n ≠ 0 := fun h0 => hh (by rw [hheq, h0, zpow_zero])
    rw [hheq]
    have hfi : sanovFactor i (FreeGroup.of () ^ n) = (![sanovA, sanovB] i) ^ n := by
      simp [sanovFactor]
    rw [hfi]
    fin_cases i <;> fin_cases j <;> first | (exact absurd rfl hij) | skip
    · exact sanovA_zpow_smul_sanovQ_subset n hn
    · exact sanovB_zpow_smul_sanovP_subset n hn

theorem sanovSubgroup_eq_range : sanovSubgroup = sanovLift.range := by
  apply le_antisymm
  · exact Subgroup.closure_le _ |>.mpr (by
      rintro _ (rfl | rfl)
      · exact ⟨Monoid.CoprodI.of (FreeGroup.of () : FreeGroup Unit) (i := 0), by
          simp [sanovLift, sanovFactor]⟩
      · exact ⟨Monoid.CoprodI.of (FreeGroup.of () : FreeGroup Unit) (i := 1), by
          simp [sanovLift, sanovFactor]⟩)
  · rintro _ ⟨w, rfl⟩
    induction w using Monoid.CoprodI.induction_on with
    | one => simp
    | of i m =>
      rw [sanovLift, Monoid.CoprodI.lift_of]
      set n := FreeGroup.freeGroupUnitEquivInt m with hndef
      have hm : m = FreeGroup.of () ^ n := by
        rw [hndef]; exact (FreeGroup.freeGroupUnitEquivInt.symm_apply_apply m).symm
      have : sanovFactor i m = (![sanovA, sanovB] i) ^ n := by
        rw [hm]; simp [sanovFactor]
      rw [this]
      refine Subgroup.zpow_mem _ ?_ _
      fin_cases i
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr rfl)
    | mul x y hx hy => simpa using sanovSubgroup.mul_mem hx hy

scoped instance sanov_isFreeGroup : IsFreeGroup ↥sanovSubgroup := by
  rw [sanovSubgroup_eq_range]
  exact IsFreeGroup.ofMulEquiv
    ((freeGroupEquivCoprodI (ι := Fin 2)).trans
      (MonoidHom.ofInjective sanovLift_injective))

theorem sanovA_mem_Gamma_two : sanovA ∈ Gamma 2 := by
  rw [Gamma_mem]; simp only [coe_sanovA, Matrix.of_apply]
  decide

theorem sanovB_mem_Gamma_two : sanovB ∈ Gamma 2 := by
  rw [Gamma_mem]; simp only [coe_sanovB, Matrix.of_apply]
  decide

theorem sanovSubgroup_le_Gamma_two : sanovSubgroup ≤ Gamma 2 :=
  Subgroup.closure_le _ |>.mpr (by
    rintro _ (rfl | rfl)
    · exact sanovA_mem_Gamma_two
    · exact sanovB_mem_Gamma_two)

theorem coe_00_mul_mod_four {g h : SL(2, ℤ)} (hg : g ∈ Gamma 2) (hh : h ∈ Gamma 2) :
    (((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
        * ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) := by
  have h01 : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod 2) = 0 := (Gamma_mem.mp hg).2.1
  have h10 : (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod 2) = 0 := (Gamma_mem.mp hh).2.2.1
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h01 h10
  have hprod : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod 4)
      * (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod 4) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast mul_dvd_mul h01 h10
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hprod, add_zero]

theorem coe_00_mod_four_of_mem_sanov {g : SL(2, ℤ)} (hg : g ∈ sanovSubgroup) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
  induction hg using Subgroup.closure_induction with
  | one => simp
  | mem x hx =>
    rcases hx with rfl | rfl
    · simp [coe_sanovA]
    · simp [coe_sanovB]
  | mul x y hx hy ihx ihy =>
    rw [coe_00_mul_mod_four (sanovSubgroup_le_Gamma_two hx) (sanovSubgroup_le_Gamma_two hy),
      ihx, ihy, one_mul]
  | inv x hx ihx =>
    have hxG2 := sanovSubgroup_le_Gamma_two hx
    have : (((x * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      simp
    rw [coe_00_mul_mod_four hxG2 (Gamma 2 |>.inv_mem hxG2), ihx, one_mul] at this
    exact this

theorem mem_sanov_of_coe_10_eq_zero {g : SL(2, ℤ)} (hg2 : g ∈ Gamma 2)
    (hg4 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1)
    (hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) : g ∈ sanovSubgroup := by
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd

  have hdet : a * d = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two, ← ha, ← hb, hc, ← hd] at this
    linarith
  have hau : a = 1 ∨ a = -1 := by
    rcases Int.isUnit_iff.mp ⟨⟨a, d, hdet, by linarith [hdet]⟩, rfl⟩ with h | h
    · left; exact h
    · right; exact h
  have ha1 : a = 1 := by
    rcases hau with h | h
    · exact h
    · exfalso; rw [h] at hg4; exact absurd hg4 (by decide)
  have hd1 : d = 1 := by rw [ha1, one_mul] at hdet; exact hdet
  have hb2 : (2 : ℤ) ∣ b := by
    have := (Gamma_mem.mp hg2).2.1
    rwa [← hb, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨k, hk⟩ := hb2
  have hg_eq : g = sanovA ^ k := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_sanovA_zpow]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.empty_val']
    · exact ha1
    · rw [show (2 * k : ℤ) = b from hk.symm]; rfl
    · exact hc
    · exact hd1
  rw [hg_eq]
  exact sanovSubgroup.zpow_mem (Subgroup.subset_closure (Or.inl rfl)) k

theorem sanovA_zpow_mul_entries (ε : ℤ) (g : SL(2, ℤ)) :
    ((sanovA ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + 2 * ε * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    ((sanovA ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [SpecialLinearGroup.coe_mul, coe_sanovA_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    simp

theorem sanovB_zpow_mul_entries (ε : ℤ) (g : SL(2, ℤ)) :
    ((sanovB ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
    ((sanovB ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = 2 * ε * (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [SpecialLinearGroup.coe_mul, coe_sanovB_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    simp

theorem exists_eps_abs_sub_lt {a c : ℤ} (hca : |c| < |a|) (hc : c ≠ 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ |a - 2 * ε * c| < |a| := by
  have ha : a ≠ 0 := by
    intro h; rw [h, abs_zero] at hca; exact absurd hca (not_lt_of_ge (abs_nonneg c))

  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hc with hc' | hc'
  · exact ⟨1, Or.inl rfl, by
      rw [abs_lt]; simp only [abs_of_neg ha', abs_of_neg hc'] at hca ⊢; omega⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [abs_lt]; simp only [abs_of_neg ha', abs_of_pos hc'] at hca ⊢; omega⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [abs_lt]; simp only [abs_of_pos ha', abs_of_neg hc'] at hca ⊢; omega⟩
  · exact ⟨1, Or.inl rfl, by
      rw [abs_lt]; simp only [abs_of_pos ha', abs_of_pos hc'] at hca ⊢; omega⟩

def sanovMeasure (g : SL(2, ℤ)) : ℕ :=
  (|(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0| + |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0|).natAbs

theorem mem_sanov_of_coe_00_mod_four {g : SL(2, ℤ)} (hg2 : g ∈ Gamma 2)
    (hg4 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1) : g ∈ sanovSubgroup := by
  induction hN : sanovMeasure g using Nat.strong_induction_on generalizing g with
  | _ N IH =>
  subst hN
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  by_cases hc0 : c = 0
  · exact mem_sanov_of_coe_10_eq_zero hg2 hg4 hc0
  have haodd : ¬ (2 : ℤ) ∣ a := by
    intro ⟨k, hk⟩
    have h1 : (a : ZMod 2) = 1 := (Gamma_mem.mp hg2).1
    rw [hk, Int.cast_mul] at h1
    have : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [this, zero_mul] at h1; exact absurd h1 (by decide)
  have hcev : (2 : ℤ) ∣ c := by
    have := (Gamma_mem.mp hg2).2.2.1
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  have hacne : |a| ≠ |c| := by
    intro heq
    rcases abs_eq_abs.mp heq with h | h
    · exact haodd (h ▸ hcev)
    · exact haodd (h ▸ (Dvd.dvd.neg_right hcev))
  have hAmem : sanovA ∈ sanovSubgroup := Subgroup.subset_closure (Or.inl rfl)
  have hBmem : sanovB ∈ sanovSubgroup := Subgroup.subset_closure (Or.inr rfl)
  rcases lt_or_gt_of_ne hacne.symm with hca | hca
  ·
    obtain ⟨ε, _, hlt⟩ := exists_eps_abs_sub_lt hca hc0
    set g' := sanovA ^ (-ε) * g with hg'
    have hg'2 : g' ∈ Gamma 2 := (Gamma 2).mul_mem ((Gamma 2).zpow_mem sanovA_mem_Gamma_two _) hg2
    have ⟨h00, h10⟩ := sanovA_zpow_mul_entries (-ε) g
    have hg'4 : ((g' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      rw [hg', h00]; push_cast
      obtain ⟨k, hk⟩ := hcev
      have h4 : (4 : ZMod 4) = 0 := by decide
      have hc4 : (c : ZMod 4) = 2 * (k : ZMod 4) := by rw [hk]; push_cast; ring
      calc ((a : ZMod 4) + 2 * (-ε) * c) = (a : ZMod 4) + (-ε * k) * 4 := by
            rw [hc4]; ring
        _ = (a : ZMod 4) := by rw [h4]; ring
        _ = 1 := hg4
    have hmeasure : sanovMeasure g' < sanovMeasure g := by
      unfold sanovMeasure; rw [hg', h00, h10]
      have heq : |a + 2 * -ε * c| = |a - 2 * ε * c| := by ring_nf
      rw [heq]
      refine Int.natAbs_lt_natAbs_of_nonneg_of_lt (by positivity) ?_
      linarith [abs_nonneg c]
    have hg'mem : g' ∈ sanovSubgroup := IH _ hmeasure hg'2 hg'4 rfl
    have heq : g = sanovA ^ ε * g' := by
      rw [hg', ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [heq]; exact sanovSubgroup.mul_mem (sanovSubgroup.zpow_mem hAmem ε) hg'mem
  ·
    have ha0 : a ≠ 0 := fun h => haodd (h ▸ dvd_zero 2)
    obtain ⟨ε, _, hlt⟩ := exists_eps_abs_sub_lt hca ha0
    set g' := sanovB ^ (-ε) * g with hg'
    have hg'2 : g' ∈ Gamma 2 := (Gamma 2).mul_mem ((Gamma 2).zpow_mem sanovB_mem_Gamma_two _) hg2
    have ⟨h00, h10⟩ := sanovB_zpow_mul_entries (-ε) g
    have hg'4 : ((g' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      rw [hg', h00]; exact hg4
    have hmeasure : sanovMeasure g' < sanovMeasure g := by
      unfold sanovMeasure; rw [hg', h00, h10]
      have heq : |2 * -ε * a + c| = |c - 2 * ε * a| := by
        rw [show 2 * -ε * a + c = c - 2 * ε * a by ring]
      rw [heq]
      refine Int.natAbs_lt_natAbs_of_nonneg_of_lt (by positivity) ?_
      linarith [abs_nonneg a]
    have hg'mem : g' ∈ sanovSubgroup := IH _ hmeasure hg'2 hg'4 rfl
    have heq : g = sanovB ^ ε * g' := by
      rw [hg', ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [heq]; exact sanovSubgroup.mul_mem (sanovSubgroup.zpow_mem hBmem ε) hg'mem

theorem gamma_four_le_gamma_two : Gamma 4 ≤ Gamma 2 := by
  intro g hg
  rw [Gamma_mem] at hg ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hg

  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · first
    | (rw [← map_intCast (ZMod.castHom (by norm_num : (2:ℕ) ∣ 4) (ZMod 2))];
       simp only [h1, h2, h3, h4, map_one, map_zero])

theorem gamma_four_le_sanov : Gamma 4 ≤ sanovSubgroup := by
  intro g hg
  refine mem_sanov_of_coe_00_mod_four (gamma_four_le_gamma_two hg) ?_
  exact (Gamma_mem.mp hg).1

scoped instance sanov_finiteIndex : sanovSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_le gamma_four_le_sanov

end ModularCurve.Sanov
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanPM
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularCurve.Sanov
open scoped MatrixGroups

def pm (Φ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Φ ∨ -g ∈ Φ}
  one_mem' := Or.inl Φ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Φ.mul_mem ha hb)
    · right
      have h := Φ.mul_mem ha hb
      rwa [mul_neg] at h
    · right
      have h := Φ.mul_mem ha hb
      rwa [neg_mul] at h
    · left
      have h := Φ.mul_mem ha hb
      rwa [neg_mul, mul_neg, neg_neg] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Φ.inv_mem ha)
    · right
      have h := Φ.inv_mem ha
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      rwa [hinv] at h

theorem le_pm (Φ : Subgroup SL(2, ℤ)) : Φ ≤ pm Φ := fun _ hg => Or.inl hg

theorem mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : g ∈ pm Φ ↔ g ∈ Φ ∨ -g ∈ Φ := Iff.rfl

theorem neg_one_mem_pm (Φ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pm Φ :=
  Or.inr (by rw [neg_neg]; exact Φ.one_mem)

theorem neg_mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : -g ∈ pm Φ ↔ g ∈ pm Φ := by
  rw [mem_pm_iff, mem_pm_iff, neg_neg]; tauto

theorem neg_one_notMem_sanov : (-1 : SL(2, ℤ)) ∉ sanovSubgroup := by
  intro h
  have h4 := coe_00_mod_four_of_mem_sanov h
  have he : (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = (3 : ZMod 4) := by
    simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, Int.cast_neg, Int.cast_one]; decide
  rw [he] at h4; exact absurd h4 (by decide)

theorem neg_one_mem_Gamma_two : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
  rw [Gamma_mem]
  simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq, Int.cast_neg, Int.cast_one]
  decide

theorem coe_00_mod_four_of_mem_Gamma_two {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 ∨
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 3 := by
  have h2 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 2) = 1 := (Gamma_mem.mp hg).1
  have hcast : (ZMod.castHom (by omega : (2 : ℕ) ∣ 4) (ZMod 2))
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
        = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 2) :=
    map_intCast _ _
  rw [h2] at hcast
  have hd : ∀ x : ZMod 4, (ZMod.castHom (by omega : (2 : ℕ) ∣ 4) (ZMod 2)) x = 1 →
      x = 1 ∨ x = 3 := by decide
  exact hd _ hcast

theorem pm_sanov_eq_Gamma_two : pm sanovSubgroup = Gamma 2 := by
  apply le_antisymm
  · rintro g (hg | hg)
    · exact sanovSubgroup_le_Gamma_two hg
    · have h := sanovSubgroup_le_Gamma_two hg
      have : g = -1 * -g := by rw [neg_mul, one_mul, neg_neg]
      rw [this]; exact (Gamma 2).mul_mem neg_one_mem_Gamma_two h
  · intro g hg
    rcases coe_00_mod_four_of_mem_Gamma_two hg with h1 | h3
    · exact Or.inl (mem_sanov_of_coe_00_mod_four hg h1)
    · refine Or.inr (mem_sanov_of_coe_00_mod_four ?_ ?_)
      · have : -g = -1 * g := (neg_one_mul g).symm
        rw [this]; exact (Gamma 2).mul_mem neg_one_mem_Gamma_two hg
      · simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h3]; decide

section SanTwo
variable (Φ : Subgroup SL(2, ℤ))

theorem neg_one_notMem_of_le_sanov (hΦ : Φ ≤ sanovSubgroup) : (-1 : SL(2, ℤ)) ∉ Φ :=
  fun h => neg_one_notMem_sanov (hΦ h)

theorem pmSubgroupOf_sanov_eq (hΦ : Φ ≤ sanovSubgroup) :
    (pm Φ).subgroupOf sanovSubgroup = Φ.subgroupOf sanovSubgroup := by
  apply le_antisymm
  · rintro g (hg | hg)
    · exact hg
    · exfalso
      have hgS : (g : SL(2, ℤ)) ∈ sanovSubgroup := g.2
      have hngS : -(g : SL(2, ℤ)) ∈ sanovSubgroup := hΦ hg
      have : (-1 : SL(2, ℤ)) = (-(g : SL(2, ℤ))) * (g : SL(2, ℤ))⁻¹ := by
        rw [neg_mul, mul_inv_cancel]
      exact neg_one_notMem_sanov (this ▸ sanovSubgroup.mul_mem hngS (sanovSubgroup.inv_mem hgS))
  · exact Subgroup.subgroupOf_mono _ (le_pm Φ)

def sanToG2 :
    ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup → ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Quotient.map' (Subgroup.inclusion sanovSubgroup_le_Gamma_two) fun a b => by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    intro h
    simpa using le_pm Φ h

@[scoped simp] theorem sanToG2_mk (g : ↥sanovSubgroup) :
    sanToG2 Φ (QuotientGroup.mk g)
      = QuotientGroup.mk (Subgroup.inclusion sanovSubgroup_le_Gamma_two g) := rfl

theorem sanToG2_injective (hΦ : Φ ≤ sanovSubgroup) : Function.Injective (sanToG2 Φ) := by
  refine Quotient.ind₂' fun a b h => ?_
  rw [sanToG2_mk, sanToG2_mk, QuotientGroup.eq] at h
  rw [QuotientGroup.eq, ← pmSubgroupOf_sanov_eq Φ hΦ]
  exact h

theorem sanToG2_surjective : Function.Surjective (sanToG2 Φ) := by
  refine Quotient.ind' fun c => ?_
  have hc2 : (c : SL(2, ℤ)) ∈ pm sanovSubgroup := by rw [pm_sanov_eq_Gamma_two]; exact c.2
  rcases hc2 with hc | hc
  · exact ⟨QuotientGroup.mk ⟨c, hc⟩, rfl⟩
  · refine ⟨QuotientGroup.mk ⟨-c, hc⟩, ?_⟩
    rw [sanToG2_mk, QuotientGroup.eq]

    have hinv : (-(c : SL(2, ℤ)))⁻¹ = -(c : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show (-(c : SL(2, ℤ)))⁻¹ * (c : SL(2, ℤ)) ∈ pm Φ
    rw [hinv, neg_mul, inv_mul_cancel]
    exact neg_one_mem_pm Φ

theorem sanToG2_bijective (hΦ : Φ ≤ sanovSubgroup) : Function.Bijective (sanToG2 Φ) :=
  ⟨sanToG2_injective Φ hΦ, sanToG2_surjective Φ⟩

noncomputable def sanToG2Equiv (hΦ : Φ ≤ sanovSubgroup) :
    ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup ≃ ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Equiv.ofBijective _ (sanToG2_bijective Φ hΦ)

theorem sanToG2_smul (s : ↥sanovSubgroup)
    (x : ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup) :
    sanToG2 Φ (s • x)
      = (Subgroup.inclusion sanovSubgroup_le_Gamma_two s) • sanToG2 Φ x := by
  refine x.induction_on fun a => ?_
  show sanToG2 Φ (QuotientGroup.mk (s * a)) = _
  rw [sanToG2_mk, map_mul]; rfl

end SanTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov"

end ModularCurve.PDPairing.SanPM
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanThree
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularCurve.Sanov
open scoped MatrixGroups

theorem sanovA_mem : sanovA ∈ sanovSubgroup := Subgroup.subset_closure (Or.inl rfl)
theorem sanovB_mem : sanovB ∈ sanovSubgroup := Subgroup.subset_closure (Or.inr rfl)

noncomputable def sanovEquiv : FreeGroup (Fin 2) ≃* ↥sanovSubgroup :=
  (freeGroupEquivCoprodI (ι := Fin 2)).trans
    ((MonoidHom.ofInjective sanovLift_injective).trans
      (MulEquiv.subgroupCongr sanovSubgroup_eq_range.symm))

theorem coe_sanovEquiv_of (i : Fin 2) :
    ((sanovEquiv (FreeGroup.of i) : ↥sanovSubgroup) : SL(2, ℤ)) = ![sanovA, sanovB] i := by
  have h1 : (freeGroupEquivCoprodI (ι := Fin 2)) (FreeGroup.of i)
      = Monoid.CoprodI.of (i := i) (FreeGroup.of ()) := by
    simp [freeGroupEquivCoprodI_apply]
  show (sanovLift ((freeGroupEquivCoprodI (ι := Fin 2)) (FreeGroup.of i))) = ![sanovA, sanovB] i
  rw [h1]
  simp [sanovLift, sanovFactor]

noncomputable def sanovBasis : FreeGroupBasis (Fin 2) ↥sanovSubgroup :=
  FreeGroupBasis.ofRepr sanovEquiv.symm

@[scoped simp] theorem sanovBasis_apply (i : Fin 2) :
    sanovBasis i = sanovEquiv (FreeGroup.of i) := by
  show sanovEquiv.symm.symm (FreeGroup.of i) = _
  rw [MulEquiv.symm_symm]

theorem coe_sanovBasis (i : Fin 2) :
    ((sanovBasis i : ↥sanovSubgroup) : SL(2, ℤ)) = ![sanovA, sanovB] i := by
  rw [sanovBasis_apply, coe_sanovEquiv_of]

theorem sanovBasis_zero : sanovBasis 0 = ⟨sanovA, sanovA_mem⟩ :=
  Subtype.ext (by rw [coe_sanovBasis]; rfl)

theorem sanovBasis_one : sanovBasis 1 = ⟨sanovB, sanovB_mem⟩ :=
  Subtype.ext (by rw [coe_sanovBasis]; rfl)

theorem closure_sanov_generators_eq_top :
    Subgroup.closure ({⟨sanovA, sanovA_mem⟩, ⟨sanovB, sanovB_mem⟩} : Set ↥sanovSubgroup) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (G := SL(2, ℤ)) (k := {sanovA, sanovB})
  delta sanovSubgroup
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

end ModularCurve.PDPairing.SanThree
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanIDX
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup Matrix ModularCurve.Sanov ModularCurve.PDPairing.SanPM
open scoped MatrixGroups ModularGroup

section IndexGammaTwo

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

theorem card_SL2_ZMod_two : Fintype.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by decide

def lowU (r : ℤ) : SL(2, ℤ) := ⟨!![1, 0; r, 1], by simp [Matrix.det_fin_two]⟩

def upE (s : ℤ) : SL(2, ℤ) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem map_lowU_val (x : ZMod 2) :
    ((SLMOD(2) (lowU (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, 0; x, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowU, Matrix.SpecialLinearGroup.map, ZMod.intCast_cast, ZMod.natCast_val]

theorem map_upE_val (x : ZMod 2) :
    ((SLMOD(2) (upE (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, x; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upE, Matrix.SpecialLinearGroup.map, ZMod.intCast_cast, ZMod.natCast_val]

theorem isUnit_col_of_det_one₂ (g : SpecialLinearGroup (Fin 2) (ZMod 2)) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) ∨
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0) := by
  have haux : ∀ a b c d : ZMod 2, a * d - b * c = 1 → IsUnit a ∨ IsUnit c := by decide
  have hdet := g.2; rw [Matrix.det_fin_two] at hdet
  exact haux _ _ _ _ hdet

def liftFn₂ (b c : ZMod 2) : SL(2, ℤ) := lowU ((c).val : ℤ) * upE ((b).val : ℤ)

theorem map_liftFn₂_aux : ∀ a b c d : ZMod 2, a * d - b * c = 1 → IsUnit a →
    ((SLMOD(2) (liftFn₂ b c)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![a, b; c, d] := by
  intro a b c d hdet hu
  simp only [liftFn₂, map_mul, SpecialLinearGroup.coe_mul, map_lowU_val, map_upE_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.empty_val']
      revert hdet hu; decide +revert

theorem mem_range_of_isUnit_00₂ (g : SpecialLinearGroup (Fin 2) (ZMod 2))
    (hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0)) :
    g ∈ (SLMOD(2)).range := by
  refine ⟨liftFn₂ ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0), ?_⟩
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1
      - (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 = 1 := by
    have := g.2; rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [map_liftFn₂_aux _ _ _ _ hdet hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem SLMOD_two_surjective : Function.Surjective (SLMOD(2)) := by
  intro g
  rcases isUnit_col_of_det_one₂ g with h0 | h1
  · exact mem_range_of_isUnit_00₂ g h0
  · have hSg : IsUnit (((SLMOD(2) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 2))
        : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) := by
      have hent : ((SLMOD(2) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 2))
          : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0
          = - (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 := by
        simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, ModularGroup.S]
        simp
      rw [hent]; exact h1.neg
    obtain ⟨y, hy⟩ := mem_range_of_isUnit_00₂ _ hSg
    exact ⟨ModularGroup.S⁻¹ * y, by
      rw [map_mul, hy, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]⟩

theorem index_Gamma_two_eq_six : (Gamma 2).index = 6 := by
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]; exact card_SL2_ZMod_two
  rw [show Gamma 2 = (SLMOD(2)).ker from rfl, Subgroup.index_ker,
    (MonoidHom.range_eq_top).mpr SLMOD_two_surjective, ← hcard,
    Nat.card_congr (Subgroup.topEquiv).toEquiv]

end IndexGammaTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"

theorem relIndex_sanov_Gamma_two_eq_two : sanovSubgroup.relIndex (Gamma 2) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨-1, neg_one_mem_Gamma_two⟩, ?_, fun b => ?_⟩
  · intro h
    exact neg_one_notMem_sanov (Subgroup.mem_subgroupOf.mp h)
  · have hbpm : (b : SL(2, ℤ)) ∈ pm sanovSubgroup := by
      rw [pm_sanov_eq_Gamma_two]; exact b.2
    rcases hbpm with hb | hb
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
    · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
      show ((b : SL(2, ℤ)) * (-1)) ∈ sanovSubgroup
      rwa [mul_neg, mul_one]

theorem sanov_index_eq_twelve : sanovSubgroup.index = 12 := by
  have h := Subgroup.relIndex_mul_index sanovSubgroup_le_Gamma_two
  rw [relIndex_sanov_Gamma_two_eq_two, index_Gamma_two_eq_six] at h
  omega

end ModularCurve.PDPairing.SanIDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"

end
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"

end InlinedSAN123
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"

section InlinedSchreier

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace Schreier
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] {V : Type*} [MulAction G V] {ι : Type*}

structure TreeTransversal (a : ι → G) (v₀ : V) where
  t : V → G
  t_smul : ∀ v, t v • v₀ = v
  t_root : t v₀ = 1
  tree : V → ι → Bool
  tree_schreier : ∀ v i, tree v i = true → t (a i • v) = a i * t v
  depth : V → ℕ
  parent : ∀ v, v ≠ v₀ → ∃ u i, depth u < depth v ∧
    ((tree u i = true ∧ a i • u = v) ∨ (tree v i = true ∧ a i • v = u))

namespace TreeTransversal

variable {a : ι → G} {v₀ : V} (T : TreeTransversal a v₀)

theorem t_mem_iff (g : G) (v : V) : (T.t (g • v))⁻¹ * g * T.t v ∈ MulAction.stabilizer G v₀ := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, T.t_smul, inv_smul_eq_iff, T.t_smul]

def x (v : V) (i : ι) : MulAction.stabilizer G v₀ := ⟨(T.t (a i • v))⁻¹ * a i * T.t v, T.t_mem_iff (a i) v⟩

@[scoped simp] theorem coe_x (v : V) (i : ι) : (T.x v i : G) = (T.t (a i • v))⁻¹ * a i * T.t v := rfl

theorem x_eq_one_of_tree (v : V) (i : ι) (h : T.tree v i = true) : T.x v i = 1 := by
  apply Subtype.ext
  rw [coe_x, T.tree_schreier v i h, OneMemClass.coe_one]
  group

def schreierClosure : Subgroup (MulAction.stabilizer G v₀) :=
  Subgroup.closure (Set.range (fun p : V × ι => T.x p.1 p.2))

theorem x_mem_schreierClosure (v : V) (i : ι) : T.x v i ∈ T.schreierClosure :=
  Subgroup.subset_closure ⟨(v, i), rfl⟩

theorem schreierClosure_eq_top (hG : Subgroup.closure (Set.range a) = ⊤) : T.schreierClosure = ⊤ := by

  have key : ∀ g : G, ∀ v : V, (T.t (g • v))⁻¹ * g * T.t v ∈ (T.schreierClosure).map (MulAction.stabilizer G v₀).subtype := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range a) := by rw [hG]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro v
      exact ⟨T.x v i, T.x_mem_schreierClosure v i, rfl⟩
    | one =>
      intro v
      rw [mul_one, one_smul, inv_mul_cancel]
      exact one_mem _
    | mul y z _ _ ihy ihz =>
      intro v
      have h := Subgroup.mul_mem _ (ihy (z • v)) (ihz v)
      rw [mul_smul]
      convert h using 1
      group
    | inv y _ ihy =>
      intro v
      have h := Subgroup.inv_mem _ (ihy (y⁻¹ • v))
      rw [smul_inv_smul] at h
      convert h using 1
      group
  rw [eq_top_iff]
  intro s _
  obtain ⟨s', hs', hs'eq⟩ := key (s : G) v₀
  have hfix : (s : G) • v₀ = v₀ := MulAction.mem_stabilizer_iff.mp s.2
  rw [hfix, T.t_root, inv_one, one_mul, mul_one] at hs'eq
  have : s' = s := Subtype.ext hs'eq
  rw [← this]
  exact hs'

def walkList (v : V) (i : ι) (k : ℕ) : List (MulAction.stabilizer G v₀) :=
  ((List.range k).map (fun j => T.x ((a i) ^ j • v) i)).reverse

theorem walkList_succ (v : V) (i : ι) (k : ℕ) :
    T.walkList v i (k + 1) = T.x ((a i) ^ k • v) i :: T.walkList v i k := by
  simp [walkList, List.range_succ]

theorem coe_prod_walkList (v : V) (i : ι) (k : ℕ) :
    ((T.walkList v i k).prod : G) = (T.t ((a i) ^ k • v))⁻¹ * (a i) ^ k * T.t v := by
  induction k with
  | zero => simp [walkList]
  | succ k ih =>
    rw [walkList_succ, List.prod_cons, Subgroup.coe_mul, ih, coe_x, ← mul_smul, ← pow_succ']
    group

theorem coe_prod_walkList_of_closed (v : V) (i : ι) (k : ℕ) (hk : (a i) ^ k • v = v) :
    ((T.walkList v i k).prod : G) = (T.t v)⁻¹ * (a i) ^ k * T.t v := by
  rw [coe_prod_walkList, hk]

theorem char_prod_walkList {R : Type*} [AddCommMonoid R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R)
    (v : V) (i : ι) (k : ℕ) :
    ψ (Additive.ofMul (T.walkList v i k).prod) = ∑ j ∈ Finset.range k, ψ (Additive.ofMul (T.x ((a i) ^ j • v) i)) := by
  induction k with
  | zero => simp [walkList]
  | succ k ih => rw [walkList_succ, List.prod_cons, ofMul_mul, map_add, ih, Finset.sum_range_succ, add_comm]

section Character

variable {R : Type*} [AddCommGroup R]

abbrev Coef (V R : Type*) [AddCommGroup R] : Type _ := V → Multiplicative R

theorem mulAutArrow_apply_apply' (g : G) (F : Coef V R) (v : V) :
    (mulAutArrow (G := G) (A := V) (M := Multiplicative R) g) F v = F (g⁻¹ • v) := rfl

variable (b : FreeGroupBasis ι G) (T : TreeTransversal (fun i => b i) v₀) (c : V → ι → R)

def letterCoef (i : ι) : Coef V R := fun w => Multiplicative.ofAdd (c ((b i)⁻¹ • w) i)

noncomputable def liftSD : G →* Coef V R ⋊[mulAutArrow] G :=
  b.lift (fun i => ⟨letterCoef b c i, b i⟩)

theorem liftSD_basis (i : ι) : liftSD b c (b i) = ⟨letterCoef b c i, b i⟩ := by
  have h := congrFun (b.lift.symm_apply_apply (fun i => (⟨letterCoef b c i, b i⟩ : Coef V R ⋊[mulAutArrow] G))) i
  exact h

theorem liftSD_right (g : G) : (liftSD b c g).right = g := by
  have hcomp : (SemidirectProduct.rightHom.comp (liftSD b c) : G →* G) = MonoidHom.id G := by
    apply b.ext_hom
    intro i
    show SemidirectProduct.rightHom (liftSD b c (b i)) = b i
    rw [liftSD_basis]
    rfl
  exact DFunLike.congr_fun hcomp g

noncomputable def F (g : G) : Coef V R := (liftSD b c g).left

theorem F_mul (g h : G) (u : V) : F b c (g * h) u = F b c g u * F b c h (g⁻¹ • u) := by
  unfold F
  rw [map_mul, SemidirectProduct.mul_left, liftSD_right]
  rfl

theorem F_one (u : V) : F b c 1 u = 1 := by
  unfold F
  rw [map_one, SemidirectProduct.one_left]
  rfl

theorem F_inv (g : G) (u : V) : F b c g⁻¹ u = (F b c g (g • u))⁻¹ := by
  have h := F_mul b c g⁻¹ g (u)
  rw [inv_mul_cancel, F_one, inv_inv] at h

  exact eq_inv_of_mul_eq_one_left h.symm

theorem F_basis (i : ι) (w : V) : F b c (b i) w = Multiplicative.ofAdd (c ((b i)⁻¹ • w) i) := by
  unfold F
  rw [liftSD_basis]
  rfl

noncomputable def pot (v : V) : R := Multiplicative.toAdd (F b c (T.t v) v)

theorem F_x (v : V) (i : ι) :
    Multiplicative.toAdd (F b c (T.x v i : G) v₀) = c v i + pot b T c v - pot b T c (b i • v) := by
  rw [coe_x, F_mul, F_mul, F_inv, F_basis]

  rw [show ((T.t (b i • v))⁻¹ * b i)⁻¹ • v₀ = v from by
      rw [mul_inv_rev, inv_inv, mul_smul, T.t_smul, inv_smul_smul],
    T.t_smul, inv_inv, T.t_smul, inv_smul_smul]
  simp only [pot, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

theorem pot_root : pot b T c v₀ = 0 := by
  simp [pot, T.t_root, F_one]

theorem pot_tree (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) (i : ι) (h : T.tree v i = true) :
    pot b T c (b i • v) = pot b T c v := by
  have hx := F_x b T c v i
  rw [T.x_eq_one_of_tree v i h, OneMemClass.coe_one, F_one, toAdd_one, hc v i h, zero_add] at hx

  exact (sub_eq_zero.mp hx.symm).symm

theorem pot_eq_zero (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) : pot b T c v = 0 := by
  induction hn : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = v₀
    · rw [hv]; exact pot_root b T c
    · obtain ⟨u, i, hdu, h⟩ := T.parent v hv
      rcases h with ⟨ht, huv⟩ | ⟨ht, hvu⟩
      · rw [← huv, pot_tree b T c hc u i ht]
        exact ih (T.depth u) (hn ▸ hdu) u rfl
      · rw [← pot_tree b T c hc v i ht, hvu]
        exact ih (T.depth u) (hn ▸ hdu) u rfl

noncomputable def character : Additive (MulAction.stabilizer G v₀) →+ R where
  toFun s := Multiplicative.toAdd (F b c ((Additive.toMul s : MulAction.stabilizer G v₀) : G) v₀)
  map_zero' := by
    show Multiplicative.toAdd (F b c ((1 : MulAction.stabilizer G v₀) : G) v₀) = 0
    rw [OneMemClass.coe_one, F_one, toAdd_one]
  map_add' s s' := by
    show Multiplicative.toAdd (F b c ((Additive.toMul s * Additive.toMul s' : MulAction.stabilizer G v₀) : G) v₀) =
      Multiplicative.toAdd (F b c ((Additive.toMul s : MulAction.stabilizer G v₀) : G) v₀) +
        Multiplicative.toAdd (F b c ((Additive.toMul s' : MulAction.stabilizer G v₀) : G) v₀)
    rw [Subgroup.coe_mul, F_mul]
    have hfix : ((Additive.toMul s : MulAction.stabilizer G v₀) : G)⁻¹ • v₀ = v₀ := by
      rw [inv_smul_eq_iff]
      exact (MulAction.mem_stabilizer_iff.mp (Additive.toMul s).2).symm
    rw [hfix, toAdd_mul]

theorem character_apply (s : MulAction.stabilizer G v₀) :
    character b c (Additive.ofMul s) = Multiplicative.toAdd (F b c (s : G) v₀) := rfl

theorem character_x (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) (i : ι) :
    character b c (Additive.ofMul (T.x v i)) = c v i := by
  rw [character_apply, F_x b T c, pot_eq_zero b T c hc, pot_eq_zero b T c hc, add_zero, sub_zero]

theorem exists_character (hc : ∀ v i, T.tree v i = true → c v i = 0) :
    ∃ ψ : Additive (MulAction.stabilizer G v₀) →+ R, ∀ v i, ψ (Additive.ofMul (T.x v i)) = c v i :=
  ⟨character b c, character_x b T c hc⟩

end Character
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree"

end TreeTransversal
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal"

section BFS

variable (a : ι → G) (v₀ : V)

def act (p : ι × Bool) : G := if p.2 then a p.1 else (a p.1)⁻¹

def wprod (l : List (ι × Bool)) : G := (l.map (act a)).prod

theorem wprod_cons (p : ι × Bool) (l : List (ι × Bool)) : wprod a (p :: l) = act a p * wprod a l := by
  simp [wprod]

def ReachN (n : ℕ) (v : V) : Prop := ∃ l : List (ι × Bool), l.length = n ∧ wprod a l • v₀ = v

theorem reachN_zero_iff (v : V) : ReachN a v₀ 0 v ↔ v = v₀ := by
  constructor
  · rintro ⟨l, hl, hv⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simpa [wprod] using hv.symm
  · rintro rfl
    exact ⟨[], rfl, by simp [wprod]⟩

theorem reach_all (hG : Subgroup.closure (Set.range a) = ⊤) (htrans : ∀ v : V, ∃ g : G, g • v₀ = v) (v : V) :
    ∃ n, ReachN a v₀ n v := by

  have key : ∀ g : G, ∀ w : V, (∃ n, ReachN a v₀ n w) ↔ (∃ n, ReachN a v₀ n (g • w)) := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range a) := by rw [hG]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro w
      constructor
      · rintro ⟨n, l, hl, hw⟩
        exact ⟨n + 1, (i, true) :: l, by simp [hl], by rw [wprod_cons, mul_smul, hw]; rfl⟩
      · rintro ⟨n, l, hl, hw⟩
        refine ⟨n + 1, (i, false) :: l, by simp [hl], ?_⟩
        rw [wprod_cons, mul_smul, hw]
        show (a i)⁻¹ • a i • w = w
        rw [inv_smul_smul]
    | one => intro w; rw [one_smul]
    | mul y z _ _ ihy ihz => intro w; rw [mul_smul, ihz w, ihy (z • w)]
    | inv y _ ihy => intro w; rw [ihy (y⁻¹ • w), smul_inv_smul]
  obtain ⟨g, hg⟩ := htrans v
  rw [← hg, ← key g v₀]
  exact ⟨0, (reachN_zero_iff a v₀ v₀).mpr rfl⟩

variable (hG : Subgroup.closure (Set.range a) = ⊤) (htrans : ∀ v : V, ∃ g : G, g • v₀ = v)

open Classical in

private noncomputable def _root_.ModularCurve.PDPairing.Schreier.depth (v : V) : ℕ := Nat.find (reach_all a v₀ hG htrans v)

p2m_export "ModularCurve.PDPairing.Schreier" "depth"
theorem depth_spec (v : V) : ReachN a v₀ (depth a v₀ hG htrans v) v := by
  classical exact Nat.find_spec (reach_all a v₀ hG htrans v)

theorem depth_le {v : V} {n : ℕ} (h : ReachN a v₀ n v) : depth a v₀ hG htrans v ≤ n := by
  classical exact Nat.find_min' _ h

theorem depth_root : depth a v₀ hG htrans v₀ = 0 :=
  Nat.le_zero.mp (depth_le a v₀ hG htrans ((reachN_zero_iff a v₀ v₀).mpr rfl))

theorem exists_parentStep (v : V) (hv : v ≠ v₀) :
    ∃ q : V × ι × Bool, depth a v₀ hG htrans q.1 < depth a v₀ hG htrans v ∧ act a (q.2.1, q.2.2) • q.1 = v := by
  obtain ⟨l, hl, hlv⟩ := depth_spec a v₀ hG htrans v
  match l, hl, hlv with
  | [], hl, hlv =>
    exfalso
    apply hv
    simpa [wprod] using hlv.symm
  | p :: l', hl, hlv =>
    refine ⟨(wprod a l' • v₀, p.1, p.2), ?_, ?_⟩
    · have hle : depth a v₀ hG htrans (wprod a l' • v₀) ≤ l'.length := depth_le a v₀ hG htrans ⟨l', rfl, rfl⟩
      have : l'.length < depth a v₀ hG htrans v := by rw [← hl]; simp
      exact lt_of_le_of_lt hle this
    · rw [← hlv, wprod_cons, mul_smul]

noncomputable def parentStep (v : V) (hv : v ≠ v₀) :
    {q : V × ι × Bool // depth a v₀ hG htrans q.1 < depth a v₀ hG htrans v ∧ act a (q.2.1, q.2.2) • q.1 = v} :=
  Classical.indefiniteDescription _ (exists_parentStep a v₀ hG htrans v hv)

open Classical in

noncomputable def tBFS (v : V) : G :=
  if hv : v = v₀ then 1
  else
    act a ((parentStep a v₀ hG htrans v hv).1.2.1, (parentStep a v₀ hG htrans v hv).1.2.2) *
      tBFS (parentStep a v₀ hG htrans v hv).1.1
termination_by depth a v₀ hG htrans v
decreasing_by exact (parentStep a v₀ hG htrans v hv).2.1

theorem tBFS_root : tBFS a v₀ hG htrans v₀ = 1 := by
  rw [tBFS, dif_pos rfl]

theorem tBFS_of_ne (v : V) (hv : v ≠ v₀) :
    tBFS a v₀ hG htrans v = act a ((parentStep a v₀ hG htrans v hv).1.2.1, (parentStep a v₀ hG htrans v hv).1.2.2) *
      tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 := by
  rw [tBFS, dif_neg hv]

theorem tBFS_smul (v : V) : tBFS a v₀ hG htrans v • v₀ = v := by
  induction hn : depth a v₀ hG htrans v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = v₀
    · subst hv; rw [tBFS_root, one_smul]
    · rw [tBFS_of_ne a v₀ hG htrans v hv, mul_smul,
        ih _ (hn ▸ (parentStep a v₀ hG htrans v hv).2.1) _ rfl]
      exact (parentStep a v₀ hG htrans v hv).2.2

open Classical in

noncomputable def treeBFS (v' : V) (i' : ι) : Bool :=
  decide (∃ (v : V) (hv : v ≠ v₀),
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true ∧ (parentStep a v₀ hG htrans v hv).1.1 = v' ∧
        (parentStep a v₀ hG htrans v hv).1.2.1 = i') ∨
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false ∧ v = v' ∧ (parentStep a v₀ hG htrans v hv).1.2.1 = i'))

theorem treeBFS_iff (v' : V) (i' : ι) : treeBFS a v₀ hG htrans v' i' = true ↔ ∃ (v : V) (hv : v ≠ v₀),
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true ∧ (parentStep a v₀ hG htrans v hv).1.1 = v' ∧
        (parentStep a v₀ hG htrans v hv).1.2.1 = i') ∨
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false ∧ v = v' ∧ (parentStep a v₀ hG htrans v hv).1.2.1 = i') := by
  classical
  unfold treeBFS
  rw [decide_eq_true_iff]

theorem child_eqs (v : V) (hv : v ≠ v₀) :
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true →
        tBFS a v₀ hG htrans v =
            a (parentStep a v₀ hG htrans v hv).1.2.1 * tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 ∧
          a (parentStep a v₀ hG htrans v hv).1.2.1 • (parentStep a v₀ hG htrans v hv).1.1 = v) ∧
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false →
        tBFS a v₀ hG htrans v =
            (a (parentStep a v₀ hG htrans v hv).1.2.1)⁻¹ * tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 ∧
          a (parentStep a v₀ hG htrans v hv).1.2.1 • v = (parentStep a v₀ hG htrans v hv).1.1) := by
  have ht := tBFS_of_ne a v₀ hG htrans v hv
  have hact := (parentStep a v₀ hG htrans v hv).2.2
  simp only [act] at ht hact
  constructor
  · intro hd
    rw [if_pos hd] at ht hact
    exact ⟨ht, hact⟩
  · intro hd
    have hd' : ¬ ((parentStep a v₀ hG htrans v hv).1.2.2 = true) := by rw [hd]; exact Bool.false_ne_true
    rw [if_neg hd'] at ht hact
    exact ⟨ht, (inv_smul_eq_iff.mp hact).symm⟩

theorem treeBFS_schreier (v' : V) (i' : ι) (h : treeBFS a v₀ hG htrans v' i' = true) :
    tBFS a v₀ hG htrans (a i' • v') = a i' * tBFS a v₀ hG htrans v' := by
  rw [treeBFS_iff] at h
  obtain ⟨v, hv, hcase⟩ := h
  have hce := child_eqs a v₀ hG htrans v hv
  rcases hcase with ⟨hd, hu, hi⟩ | ⟨hd, hvv, hi⟩
  · obtain ⟨ht, hact⟩ := hce.1 hd
    rw [hu, hi] at ht hact
    rw [hact, ht]
  · obtain ⟨ht, hact⟩ := hce.2 hd
    rw [hi] at ht hact
    subst hvv
    rw [hact, ht, mul_inv_cancel_left]

noncomputable def bfsTransversal : TreeTransversal a v₀ where
  t := tBFS a v₀ hG htrans
  t_smul := tBFS_smul a v₀ hG htrans
  t_root := tBFS_root a v₀ hG htrans
  tree := treeBFS a v₀ hG htrans
  tree_schreier := treeBFS_schreier a v₀ hG htrans
  depth := depth a v₀ hG htrans
  parent v hv := by
    refine ⟨(parentStep a v₀ hG htrans v hv).1.1, (parentStep a v₀ hG htrans v hv).1.2.1,
      (parentStep a v₀ hG htrans v hv).2.1, ?_⟩
    have hce := child_eqs a v₀ hG htrans v hv
    cases hd : (parentStep a v₀ hG htrans v hv).1.2.2
    · right
      refine ⟨(treeBFS_iff a v₀ hG htrans _ _).mpr ⟨v, hv, Or.inr ⟨hd, rfl, rfl⟩⟩, (hce.2 hd).2⟩
    · left
      refine ⟨(treeBFS_iff a v₀ hG htrans _ _).mpr ⟨v, hv, Or.inl ⟨hd, rfl, rfl⟩⟩, (hce.1 hd).2⟩

end BFS
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal"

namespace TreeTransversal

variable {a : ι → G} {v₀ : V} (T : TreeTransversal a v₀)

noncomputable def sx (w : V) (p : ι × Bool) : MulAction.stabilizer G v₀ :=
  if p.2 then T.x w p.1 else (T.x ((a p.1)⁻¹ • w) p.1)⁻¹

theorem sx_true (w : V) (i : ι) : T.sx w (i, true) = T.x w i := by simp [sx]

theorem sx_false (w : V) (i : ι) : T.sx w (i, false) = (T.x ((a i)⁻¹ • w) i)⁻¹ := by simp [sx]

theorem coe_sx (w : V) (p : ι × Bool) : (T.sx w p : G) = (T.t (act a p • w))⁻¹ * act a p * T.t w := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [sx_false, Subgroup.coe_inv, coe_x, smul_inv_smul]
    simp only [act, Bool.false_eq_true, ↓reduceIte]
    group
  · rw [sx_true, coe_x]
    simp [act]

noncomputable def wordWalk (v : V) : List (ι × Bool) → MulAction.stabilizer G v₀
  | [] => 1
  | p :: l => T.sx (wprod a l • v) p * wordWalk v l

theorem wordWalk_nil (v : V) : T.wordWalk v [] = 1 := rfl

theorem wordWalk_cons (v : V) (p : ι × Bool) (l : List (ι × Bool)) :
    T.wordWalk v (p :: l) = T.sx (wprod a l • v) p * T.wordWalk v l := rfl

theorem coe_wordWalk (v : V) (l : List (ι × Bool)) :
    (T.wordWalk v l : G) = (T.t (wprod a l • v))⁻¹ * wprod a l * T.t v := by
  induction l with
  | nil => simp [wordWalk, wprod]
  | cons p l ih => rw [wordWalk_cons, Subgroup.coe_mul, ih, coe_sx, wprod_cons, mul_smul]; group

theorem coe_wordWalk_of_closed (v : V) (l : List (ι × Bool)) (h : wprod a l • v = v) :
    (T.wordWalk v l : G) = (T.t v)⁻¹ * wprod a l * T.t v := by
  rw [coe_wordWalk, h]

theorem char_wordWalk_cons {R : Type*} [AddCommGroup R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R)
    (v : V) (p : ι × Bool) (l : List (ι × Bool)) :
    ψ (Additive.ofMul (T.wordWalk v (p :: l))) = ψ (Additive.ofMul (T.sx (wprod a l • v) p)) + ψ (Additive.ofMul (T.wordWalk v l)) := by
  rw [wordWalk_cons, ofMul_mul, map_add]

theorem char_sx {R : Type*} [AddCommGroup R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R) (w : V) (p : ι × Bool) :
    ψ (Additive.ofMul (T.sx w p)) =
      if p.2 then ψ (Additive.ofMul (T.x w p.1)) else -ψ (Additive.ofMul (T.x ((a p.1)⁻¹ • w) p.1)) := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [sx_false, ofMul_inv, map_neg]; simp
  · rw [sx_true]; simp

end TreeTransversal
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal"

end ModularCurve.PDPairing.Schreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal"

end InlinedSchreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

section Aux2CuspTower

set_option autoImplicit false

open MulAction Function

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace CuspTower
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] (g : G) (K' K : Subgroup G)

abbrev ACusp : Type _ := Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ K))

def acuspGen (q : ACusp g K) : K :=
  ⟨q.out.out⁻¹ * g ^ minimalPeriod (g • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem K g q.out⟩

abbrev InnerOrbit (_hle : K' ≤ K) (q : ACusp g K) : Type _ :=
  Quotient (orbitRel (Subgroup.zpowers (acuspGen g K q)) (K ⧸ K'.subgroupOf K))

variable {K' K}

def towerLift (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) : G :=
  (q.out.out : G) * ((o.out.out : K) : G)

theorem towerLift_mk_K (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    QuotientGroup.mk (s := K) (towerLift g hle q o) = q.out := by
  rw [towerLift, ← QuotientGroup.out_eq' q.out, QuotientGroup.eq]
  simp [(o.out.out : K).2]

def towerFn (hle : K' ≤ K) (p : Σ q : ACusp g K, InnerOrbit g K' K hle q) : ACusp g K' :=
  Quotient.mk _ (QuotientGroup.mk (s := K') (towerLift g hle p.1 p.2))

section Helpers

variable (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
variable (q : ACusp g K) (o : InnerOrbit g K' K hle q)

local notation "m" => minimalPeriod (g • ·) q.out
local notation "p₀" => towerLift g hle q o

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem zpow_smul_towerLift_eq_iff (n : ℤ) :
    g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') p₀ ↔
      p₀⁻¹ * g ^ n * p₀ ∈ K' := by
  rw [show g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') (g ^ n * p₀) from rfl,
    eq_comm, QuotientGroup.eq]
  constructor
  · intro h; have := h; rwa [show p₀⁻¹ * (g ^ n * p₀) = p₀⁻¹ * g ^ n * p₀ by group] at this
  · intro h; rwa [show p₀⁻¹ * g ^ n * p₀ = p₀⁻¹ * (g ^ n * p₀) by group] at h

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem towerLift_conj_zpow (n : ℤ) :
    p₀⁻¹ * g ^ n * p₀ =
      ((o.out.out : K) : G)⁻¹ * (q.out.out⁻¹ * g ^ n * q.out.out) * ((o.out.out : K) : G) := by
  unfold towerLift; group

omit [K.FiniteIndex] in

theorem conj_pow_mem_K_iff (n : ℕ) :
    q.out.out⁻¹ * g ^ n * q.out.out ∈ K ↔ m ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
    MulAction.Quotient.mk_smul_out, eq_comm, pow_smul_eq_iff_minimalPeriod_dvd]

omit [K.FiniteIndex] in

theorem conj_pow_eq_acuspGen_pow (j : ℕ) :
    q.out.out⁻¹ * g ^ (m * j) * q.out.out = ((acuspGen g K q : K) : G) ^ j := by
  rw [pow_mul]
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [acuspGen]; group

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem acuspGen_pow_smul_eq_iff (j : ℕ) :
    (acuspGen g K q) ^ j • o.out = o.out ↔
      ((o.out.out : K) : G)⁻¹ * ((acuspGen g K q : K) : G) ^ j * ((o.out.out : K) : G) ∈ K' := by
  have h : (o.out.out : K)⁻¹ * (acuspGen g K q) ^ j * o.out.out ∈ K'.subgroupOf K ↔
      (acuspGen g K q) ^ j • o.out = o.out := by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
      MulAction.Quotient.mk_smul_out, eq_comm]
  rw [← h, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, InvMemClass.coe_inv]

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem pow_smul_towerLift_eq_iff (n : ℕ) :
    g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') p₀ ↔
      ∃ j, n = m * j ∧ (acuspGen g K q) ^ j • o.out = o.out := by
  rw [show (g : G) ^ n = g ^ (n : ℤ) from (zpow_natCast g n).symm,
    zpow_smul_towerLift_eq_iff, towerLift_conj_zpow, zpow_natCast]
  constructor
  · intro h
    have hK : q.out.out⁻¹ * g ^ n * q.out.out ∈ K := by
      have hK' : ((o.out.out : K) : G)⁻¹ * (q.out.out⁻¹ * g ^ n * q.out.out) *
          ((o.out.out : K) : G) ∈ K := hle h
      have := K.mul_mem (K.mul_mem (o.out.out : K).2 hK') (K.inv_mem (o.out.out : K).2)
      simpa [mul_assoc] using this
    obtain ⟨j, hj⟩ := (conj_pow_mem_K_iff g q n).mp hK
    refine ⟨j, hj, ?_⟩
    rw [acuspGen_pow_smul_eq_iff, ← conj_pow_eq_acuspGen_pow g q j, ← hj]
    exact h
  · rintro ⟨j, hj, hfix⟩
    subst hj
    rw [conj_pow_eq_acuspGen_pow g q j]
    exact (acuspGen_pow_smul_eq_iff g hle q o j).mp hfix

omit [K.FiniteIndex] in

theorem conj_zpow_mem_K_iff (n : ℤ) :
    q.out.out⁻¹ * g ^ n * q.out.out ∈ K ↔ (m : ℤ) ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
    MulAction.Quotient.mk_smul_out, eq_comm, zpow_smul_eq_iff_minimalPeriod_dvd]

omit [K.FiniteIndex] in

theorem conj_zpow_eq_acuspGen_zpow (j : ℤ) :
    q.out.out⁻¹ * g ^ ((m : ℤ) * j) * q.out.out = ((acuspGen g K q : K) : G) ^ j := by
  have h1 : ((acuspGen g K q : K) : G) = q.out.out⁻¹ * g ^ (m : ℤ) * q.out.out := by
    simp [acuspGen, zpow_natCast]
  rw [h1, zpow_mul]
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, zpow_add_one, ← ih]; group
  | pred k ih => rw [zpow_sub_one, zpow_sub_one, ← ih]; group

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem minimalPeriod_zpow_smul (n : ℤ) (x : G ⧸ K') :
    minimalPeriod (g • ·) (g ^ n • x) = minimalPeriod (g • ·) x := by
  have hcomm : ∀ (a : ℕ), g ^ a • g ^ n • x = g ^ n • g ^ a • x := fun a => by
    rw [← mul_smul, ← mul_smul, ← zpow_natCast g a, ← zpow_add, ← zpow_add, add_comm]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hcomm, (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl]
  · have h := (pow_smul_eq_iff_minimalPeriod_dvd (a := g)
      (b := g ^ n • x) (n := minimalPeriod (g • ·) (g ^ n • x))).mpr dvd_rfl
    rw [hcomm] at h
    exact smul_left_cancel _ h

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem zpow_smul_mk_eq_mk_iff (n : ℤ) (a b : G) :
    g ^ n • QuotientGroup.mk (s := K') a = QuotientGroup.mk (s := K') b ↔
      b⁻¹ * g ^ n * a ∈ K' := by
  rw [show g ^ n • QuotientGroup.mk (s := K') a = QuotientGroup.mk (s := K') (g ^ n * a) from rfl,
    eq_comm, QuotientGroup.eq, mul_assoc]

end Helpers
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

theorem towerFn_surjective (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    Function.Surjective (towerFn g hle) := by
  intro q'
  set x := q'.out.out with hx

  set q : ACusp g K := Quotient.mk _ (QuotientGroup.mk (s := K) x) with hq

  have hqout : (Quotient.mk _ q.out : ACusp g K) = Quotient.mk _ (QuotientGroup.mk (s := K) x) := by
    rw [Quotient.out_eq]
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at hqout
  obtain ⟨h, hh⟩ := hqout
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K) x = q.out := hng ▸ hh
  clear hng hh h
  have hκmem : q.out.out⁻¹ * g ^ n * x ∈ K :=
    (zpow_smul_mk_eq_mk_iff (K' := K) g n x q.out.out).mp (by rw [hn', QuotientGroup.out_eq'])

  set κ : K := ⟨q.out.out⁻¹ * g ^ n * x, hκmem⟩ with hκ
  set o : InnerOrbit g K' K hle q :=
    Quotient.mk _ (QuotientGroup.mk (s := K'.subgroupOf K) κ) with ho
  refine ⟨⟨q, o⟩, ?_⟩

  have hoout : (Quotient.mk _ o.out : InnerOrbit g K' K hle q)
      = Quotient.mk _ (QuotientGroup.mk (s := K'.subgroupOf K) κ) := by
    rw [Quotient.out_eq]
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at hoout
  obtain ⟨h, hh⟩ := hoout
  obtain ⟨j, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hj' : (acuspGen g K q) ^ j • QuotientGroup.mk (s := K'.subgroupOf K) κ = o.out := hng ▸ hh
  clear hng hh h
  have hk'mem : (o.out.out : K)⁻¹ * (acuspGen g K q) ^ j * κ ∈ K'.subgroupOf K := by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
    exact hj'.symm

  show Quotient.mk _ (QuotientGroup.mk (s := K') (towerLift g hle q o)) = q'
  rw [← Quotient.out_eq q', Quotient.eq, orbitRel_apply, mem_orbit_iff]
  set mj := (minimalPeriod (g • ·) q.out : ℤ) * j with hmj
  refine ⟨⟨g ^ (mj + n), mj + n, rfl⟩, ?_⟩
  show g ^ (mj + n) • q'.out = QuotientGroup.mk (s := K') (towerLift g hle q o)
  rw [← QuotientGroup.out_eq' q'.out, ← hx, zpow_smul_mk_eq_mk_iff]

  have hkey : q.out.out⁻¹ * g ^ (mj + n) * x
      = ((acuspGen g K q : K) : G) ^ j * (κ : G) := by
    rw [hκ, hmj, ← conj_zpow_eq_acuspGen_zpow g q j]; push_cast; group
  have heq : (towerLift g hle q o)⁻¹ * g ^ (mj + n) * x
      = ((o.out.out : K) : G)⁻¹ * (((acuspGen g K q : K) : G) ^ j * (κ : G)) := by
    unfold towerLift; rw [← hkey]; group
  rw [heq]
  have := Subgroup.mem_subgroupOf.mp hk'mem
  simpa [mul_assoc] using this

theorem towerFn_injective (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    Function.Injective (towerFn g hle) := by
  rintro ⟨q₁, o₁⟩ ⟨q₂, o₂⟩ heq
  rw [towerFn, towerFn, Quotient.eq, orbitRel_apply, mem_orbit_iff] at heq
  obtain ⟨h, hn⟩ := heq
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K') (towerLift g hle q₂ o₂)
      = QuotientGroup.mk (s := K') (towerLift g hle q₁ o₁) := hng ▸ hn
  clear hng hn h
  have hmemK' := (zpow_smul_mk_eq_mk_iff g n (towerLift g hle q₂ o₂) (towerLift g hle q₁ o₁)).mp hn'

  set α := q₁.out.out⁻¹ * g ^ n * q₂.out.out with hα
  have hmemK'2 : ((o₁.out.out : K) : G)⁻¹ * α * ((o₂.out.out : K) : G) ∈ K' := by
    have heq : (towerLift g hle q₁ o₁)⁻¹ * g ^ n * towerLift g hle q₂ o₂
        = ((o₁.out.out : K) : G)⁻¹ * α * ((o₂.out.out : K) : G) := by
      unfold towerLift; rw [hα]; group
    rwa [heq] at hmemK'
  clear hmemK'

  have hαK : α ∈ K := by
    have hmemK := hle hmemK'2
    have := K.mul_mem (K.mul_mem (o₁.out.out : K).2 hmemK) (K.inv_mem (o₂.out.out : K).2)
    simpa [mul_assoc] using this
  have hq1out : g ^ n • q₂.out = q₁.out := by
    rw [← QuotientGroup.out_eq' q₂.out, ← QuotientGroup.out_eq' q₁.out,
      zpow_smul_mk_eq_mk_iff (K' := K)]
    exact hαK
  have hqeq : q₁ = q₂ := by
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, ← hq1out]
    exact Quotient.sound ⟨⟨g ^ n, n, rfl⟩, rfl⟩

  subst hqeq
  have hmj : (minimalPeriod (g • ·) q₁.out : ℤ) ∣ n := (conj_zpow_mem_K_iff g q₁ n).mp hαK
  obtain ⟨j, hj⟩ := hmj
  have hαeq : α = ((acuspGen g K q₁ : K) : G) ^ j := by
    rw [hα, hj, conj_zpow_eq_acuspGen_zpow]
  rw [hαeq] at hmemK'2

  have hoeq : (acuspGen g K q₁) ^ j • o₂.out = o₁.out := by
    rw [← QuotientGroup.out_eq' o₂.out, ← QuotientGroup.out_eq' o₁.out,
      show (acuspGen g K q₁) ^ j • QuotientGroup.mk (s := K'.subgroupOf K) o₂.out.out
        = QuotientGroup.mk (s := K'.subgroupOf K) ((acuspGen g K q₁) ^ j * o₂.out.out) from rfl,
      eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hmemK'2
  congr 1
  rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂, ← hoeq]
  exact Quotient.sound ⟨⟨(acuspGen g K q₁) ^ j, j, rfl⟩, rfl⟩

def towerEquiv (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    (Σ q : ACusp g K, InnerOrbit g K' K hle q) ≃ ACusp g K' :=
  Equiv.ofBijective (towerFn g hle) ⟨towerFn_injective g hle, towerFn_surjective g hle⟩

theorem minimalPeriod_towerLift (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    minimalPeriod (g • ·) (QuotientGroup.mk (s := K') (towerLift g hle q o))
      = minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out := by
  haveI : Finite (G ⧸ K') := K'.finite_quotient_of_finiteIndex
  haveI : Finite (G ⧸ K) := K.finite_quotient_of_finiteIndex
  haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
  set m := minimalPeriod (g • ·) q.out with hm
  set k := minimalPeriod ((acuspGen g K q) • ·) o.out with hk
  apply Nat.dvd_antisymm
  ·
    rw [← pow_smul_eq_iff_minimalPeriod_dvd, pow_smul_towerLift_eq_iff]
    exact ⟨k, rfl, (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl⟩
  ·
    have hper : g ^ (minimalPeriod (g • ·) (QuotientGroup.mk (s := K') (towerLift g hle q o)))
        • QuotientGroup.mk (s := K') (towerLift g hle q o)
        = QuotientGroup.mk (s := K') (towerLift g hle q o) :=
      (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
    obtain ⟨j, hj, hfix⟩ := (pow_smul_towerLift_eq_iff g hle q o _).mp hper
    obtain ⟨l, hl⟩ := (pow_smul_eq_iff_minimalPeriod_dvd).mp hfix
    exact ⟨l, by rw [hj, hl]; ring⟩

theorem acuspGen_towerEquiv_conj (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ∃ c' : K',
      ((acuspGen g K' (towerEquiv g hle ⟨q, o⟩) : K') : G) =
        (c' : G) *
          (((o.out.out : K) : G)⁻¹ *
            ((acuspGen g K q : K) : G) ^ minimalPeriod ((acuspGen g K q) • ·) o.out *
            ((o.out.out : K) : G)) *
          (c' : G)⁻¹ := by
  haveI : Finite (G ⧸ K') := K'.finite_quotient_of_finiteIndex
  set q' := towerEquiv g hle ⟨q, o⟩ with hq'
  set p₀ := towerLift g hle q o with hp₀

  have hq'mk : q' = Quotient.mk _ (QuotientGroup.mk (s := K') p₀) := by
    rw [hq', towerEquiv, Equiv.ofBijective_apply]; rfl
  have horb : (Quotient.mk _ q'.out : ACusp g K')
      = Quotient.mk _ (QuotientGroup.mk (s := K') p₀) := by
    rw [Quotient.out_eq]; exact hq'mk
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at horb
  obtain ⟨h, hn⟩ := horb
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K') p₀ = q'.out := hng ▸ hn
  clear hng hn h

  have hφ' : (g ^ n * p₀)⁻¹ * q'.out.out ∈ K' := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← hn']; rfl
  set φ' : K' := ⟨(g ^ n * p₀)⁻¹ * q'.out.out, hφ'⟩ with hφ'def
  have hout : q'.out.out = g ^ n * p₀ * (φ' : G) := by
    rw [hφ'def]; simp [mul_assoc]
  refine ⟨⟨(φ' : G)⁻¹, K'.inv_mem φ'.2⟩, ?_⟩

  have hm' : minimalPeriod (g • ·) q'.out
      = minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out := by
    rw [← hn', minimalPeriod_zpow_smul, minimalPeriod_towerLift]

  show q'.out.out⁻¹ * g ^ minimalPeriod (g • ·) q'.out * q'.out.out = _
  rw [hout, hm', ← conj_pow_eq_acuspGen_pow g q (minimalPeriod ((acuspGen g K q) • ·) o.out)]
  have hconj := towerLift_conj_zpow g hle q o
    ((minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out : ℕ) : ℤ)
  rw [zpow_natCast] at hconj
  rw [← hp₀] at hconj
  rw [show ((o.out.out : K) : G)⁻¹ *
      (q.out.out⁻¹ * g ^ (minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out)
        * q.out.out) * ((o.out.out : K) : G)
      = p₀⁻¹ * g ^ (minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out) * p₀
    from hconj.symm]
  group

theorem cusp_tower_abstract (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    ∃ e : ACusp g K' ≃ Σ q : ACusp g K, InnerOrbit g K' K hle q,
      ∀ (q : ACusp g K) (o : InnerOrbit g K' K hle q),
        ∃ c' : K',
          ((acuspGen g K' (e.symm ⟨q, o⟩) : K') : G) =
            (c' : G) *
              (((o.out.out : K) : G)⁻¹ *
                ((acuspGen g K q : K) : G) ^ minimalPeriod ((acuspGen g K q) • ·) o.out *
                ((o.out.out : K) : G)) *
              (c' : G)⁻¹ := by
  refine ⟨(towerEquiv g hle).symm, ?_⟩
  intro q o
  simpa using acuspGen_towerEquiv_conj g hle q o

end ModularCurve.PDPairing.CuspTower
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end Aux2CuspTower
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

section Aux4PDU

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace Period
p2m_export "ModularCurve.Period" "IsParabolicHom parabolicHoms mem_parabolicHoms_iff"
p2m_open "ModularCurve.Period ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

theorem IsParabolicHom.apply_T_zpow_eq_zero {A : Type*} [AddCommGroup A] {φ : Additive Γ →+ A}
    (hφ : IsParabolicHom Γ φ) (n : ℤ) (hT : ModularGroup.T ^ n ∈ Γ) :
    φ (Additive.ofMul ⟨ModularGroup.T ^ n, hT⟩) = 0 := by
  refine hφ _ ?_
  have : ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] :=
    ModularGroup.coe_T_zpow n
  rw [this, Matrix.trace_fin_two_of]
  norm_num

theorem IsParabolicHom.apply_neg_one_eq_zero {A : Type*} [AddCommGroup A] {φ : Additive Γ →+ A}
    (hφ : IsParabolicHom Γ φ) (h : (-1 : SL(2, ℤ)) ∈ Γ) :
    φ (Additive.ofMul ⟨-1, h⟩) = 0 := by
  refine hφ _ ?_
  have : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -1 := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [this]
  simp

end ModularCurve.Period
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
p2m_open "ModularCurve.PDPairing ModularCurve"

section Gamma0Hecke

variable (M : ℕ) (ℓ : ℕ) (A : Type*) [AddCommGroup A]

noncomputable def heckeT0L (R : Type*) [Semiring R] [Module R A] [NeZero ℓ] :
    (Additive ↥(Gamma0 M) →+ A) →ₗ[R] (Additive ↥(Gamma0 M) →+ A) where
  toFun := heckeT0 M ℓ A
  map_add' := (heckeT0 M ℓ A).map_add
  map_smul' r φ := by
    ext g
    simp only [heckeT0_apply, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.smul_apply,
      MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
      MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd,
      Finset.smul_sum, RingHom.id_apply]

end Gamma0Hecke
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

section ParRestrict

p2m_open "ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

theorem trace_conjLowerMat (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    ((conjLowerMat d A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  show (conjLowerMat d A h) 0 0 + (conjLowerMat d A h) 1 1 = A 0 0 + A 1 1
  simp [conjLowerMat]

theorem trace_conjUpperMat (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    ((conjUpperMat ℓ A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  show (conjUpperMat ℓ A h) 0 0 + (conjUpperMat ℓ A h) 1 1 = A 0 0 + A 1 1
  simp [conjUpperMat]

theorem sq_sub_one_eq_zero_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) : (M - 1) ^ 2 = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  ext i j
  rw [sq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination M 0 0 * htr - hdet
      | linear_combination M 0 1 * htr
      | linear_combination M 1 0 * htr
      | linear_combination M 1 1 * htr - hdet

theorem trace_pow_eq_two_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) (n : ℕ) : (M ^ n).trace = 2 := by
  have hNN : (M - 1) * (M - 1) = 0 := by
    rw [← sq]; exact sq_sub_one_eq_zero_of_trace_eq_two M hdet htr
  have hsplit : (1 : Matrix (Fin 2) (Fin 2) ℤ) + (M - 1) = M := by abel
  have hNM : (M - 1) * M = M - 1 := by
    calc (M - 1) * M = (M - 1) * (1 + (M - 1)) := by rw [hsplit]
      _ = (M - 1) * 1 + (M - 1) * (M - 1) := by rw [mul_add]
      _ = M - 1 := by rw [mul_one, hNN, add_zero]
  have hpow : ∀ m : ℕ, M ^ m = 1 + m • (M - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      calc M ^ (k + 1) = M ^ k * M := pow_succ M k
        _ = (1 + k • (M - 1)) * M := by rw [ih]
        _ = 1 * M + (k • (M - 1)) * M := by rw [add_mul]
        _ = M + k • ((M - 1) * M) := by rw [one_mul, smul_mul_assoc]
        _ = M + k • (M - 1) := by rw [hNM]
        _ = 1 + (k + 1) • (M - 1) := by
            rw [succ_nsmul, ← hsplit]
            abel
  rw [hpow n, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, htr, Matrix.trace_one]
  simp [Fintype.card_fin]

theorem sq_trace_pow_eq_four (A : SL(2, ℤ))
    (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) (n : ℕ) :
    (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M.det = 1 := A.2
  have hcoe : (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = M ^ n := by
    simp [hM]
  rw [hcoe]
  have htr : M.trace = 2 ∨ M.trace = -2 := by
    have h0 : (M.trace - 2) * (M.trace + 2) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases htr with h2 | hm2
  · rw [trace_pow_eq_two_of_trace_eq_two M hdet h2 n]; norm_num
  · have hdetneg : (-M).det = 1 := by
      rw [Matrix.det_neg]
      simp [hdet, Fintype.card_fin]
    have htrneg : (-M).trace = 2 := by rw [Matrix.trace_neg, hm2]; ring
    have hkey := trace_pow_eq_two_of_trace_eq_two (-M) hdetneg htrneg n
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_pow] at hkey
      rw [hkey]; norm_num
    · rw [ho.neg_pow, Matrix.trace_neg] at hkey
      have hm : (M ^ n).trace = -2 := by linarith
      rw [hm]; norm_num

variable (R : Type*) [CommRing R] (M M' d : ℕ)

theorem trace_conj_SL (b c : SL(2, ℤ)) :
    ((b⁻¹ * c * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_comm, ← mul_assoc, ← coe_mul, mul_inv_cancel,
    coe_one, one_mul]

theorem sq_trace_conj_pow (b γA : ↥(Gamma0 M)) (p : ℕ)
    (hγ : ((γA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    (((b⁻¹ * γA ^ p * b : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  have hcoe : ((b⁻¹ * γA ^ p * b : ↥(Gamma0 M)) : SL(2, ℤ))
      = ((b : SL(2, ℤ)))⁻¹ * ((γA : SL(2, ℤ))) ^ p * (b : SL(2, ℤ)) := by
    norm_cast
  rw [hcoe, trace_conj_SL]
  exact sq_trace_pow_eq_four γA hγ p

theorem conjL0_parabolic_vanish (ℓ : ℕ) [NeZero ℓ]
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R)
    (x : ↥(Gamma0HUpper M ℓ))
    (hx : (((x : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    φ (Additive.ofMul (conjL0 M ℓ x)) = 0 := by
  refine hφ _ ?_
  show ((conjUpperMat ℓ ((x : ↥(Gamma0 M)) : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ x)
      : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_conjUpperMat]
  exact hx

theorem pushChar0_parabolic_vanish [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (ψ : Additive ↥(Gamma0 M') →+ R) (hψ : ψ ∈ parabolicHoms R (Gamma0 M') R)
    (e : ↥((iotaDeg0 M M' d hMM' hdd).range))
    (he : (((e : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    pushChar0 M M' d R hMM' hdd ψ (Additive.ofMul e) = 0 := by
  show ψ (Additive.ofMul (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e)) = 0
  refine hψ _ ?_
  have happ : iotaDeg0 M M' d hMM' hdd (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e) = (e : ↥(Gamma0 M)) := by
    have h := MulEquiv.apply_symm_apply ((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)) e
    exact congrArg Subtype.val h
  rw [← trace_conjLowerMat d ((((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e : ↥(Gamma0 M')) : SL(2, ℤ))
      (dvd_entry0 M M' d hMM' hdd _)]
  show (((iotaDeg0 M M' d hMM' hdd (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e) : ↥(Gamma0 M)) : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [happ]
  exact he

theorem iDeg0_mem_parabolicHoms [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R) :
    iDeg0 M M' d R R hMM' hdd φ ∈ parabolicHoms R (Gamma0 M') R := by
  intro γ' hγ'
  show φ (Additive.ofMul (iotaDeg0 M M' d hMM' hdd γ')) = 0
  refine hφ (iotaDeg0 M M' d hMM' hdd γ') ?_
  show ((conjLowerMat d (γ' : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ') : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_conjLowerMat]
  exact hγ'

theorem jDeg0_mem_parabolicHoms [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (ψ : Additive ↥(Gamma0 M') →+ R) (hψ : ψ ∈ parabolicHoms R (Gamma0 M') R) :
    jDeg0 M M' d R R hMM' hdd ψ ∈ parabolicHoms R (Gamma0 M) R := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (↥(Subgroup.zpowers γ))
      (↥(Gamma0 M) ⧸ (iotaDeg0 M M' d hMM' hdd).range))) := Fintype.ofFinite _
  show Multiplicative.toAdd
      (MonoidHom.transfer
        (AddMonoidHom.toMultiplicativeRight (pushChar0 M M' d R hMM' hdd ψ))
        (Additive.toMul (Additive.ofMul γ))) = 0
  rw [toMul_ofMul, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  exact pushChar0_parabolic_vanish R M M' d hMM' hdd ψ hψ _
    (sq_trace_conj_pow M q.out.out γ _ hγ)

theorem heckeT0_mem_parabolicHoms (ℓ : ℕ) [NeZero ℓ]
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R) :
    heckeT0 M ℓ R φ ∈ parabolicHoms R (Gamma0 M) R := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (↥(Subgroup.zpowers γ))
      (↥(Gamma0 M) ⧸ Gamma0HUpper M ℓ))) := Fintype.ofFinite _
  show Multiplicative.toAdd
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ))
        (Additive.toMul (Additive.ofMul γ))) = 0
  rw [toMul_ofMul, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  exact conjL0_parabolic_vanish R M ℓ φ hφ _ (sq_trace_conj_pow M q.out.out γ _ hγ)

def iPar [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ↥(parabolicHoms R (Gamma0 M) R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M') R) :=
  (iDeg0 M M' d R R hMM' hdd).restrict
    (fun φ hφ => iDeg0_mem_parabolicHoms R M M' d hMM' hdd φ hφ)

noncomputable def jPar [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ↥(parabolicHoms R (Gamma0 M') R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M) R) :=
  (jDeg0 M M' d R R hMM' hdd).restrict
    (fun ψ hψ => jDeg0_mem_parabolicHoms R M M' d hMM' hdd ψ hψ)

noncomputable def TPar (ℓ : ℕ) [NeZero ℓ] :
    ↥(parabolicHoms R (Gamma0 M) R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M) R) :=
  (heckeT0L M ℓ R R).restrict (fun φ hφ => heckeT0_mem_parabolicHoms R M ℓ φ hφ)

end ParRestrict
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end ModularCurve.PDPairing
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end Aux4PDU
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

section Aux2IDX

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace IDX
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

theorem card_SL2_ZMod_four : Fintype.card (SpecialLinearGroup (Fin 2) (ZMod 4)) = 48 := by decide

theorem isUnit_col_of_det_aux :
    ∀ a b c d : ZMod 4, a * d - b * c = 1 → IsUnit a ∨ IsUnit c := by decide

theorem isUnit_col_of_det_one (g : SpecialLinearGroup (Fin 2) (ZMod 4)) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0) ∨
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0) := by
  have hdet := g.2; rw [Matrix.det_fin_two] at hdet
  exact isUnit_col_of_det_aux _ _ _ _ hdet

def U (r : ℤ) : SL(2, ℤ) := ⟨!![1, 0; r, 1], by simp [Matrix.det_fin_two]⟩

def E (s : ℤ) : SL(2, ℤ) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem map_U_val (x : ZMod 4) :
    ((SLMOD(4) (U (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![1, 0; x, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.SpecialLinearGroup.map, ZMod.natCast_val, ZMod.intCast_cast]

theorem map_E_val (x : ZMod 4) :
    ((SLMOD(4) (E (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![1, x; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.SpecialLinearGroup.map, ZMod.natCast_val, ZMod.intCast_cast]

theorem map_neg_one :
    ((SLMOD(4) (-1 : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![-1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map]

def liftFn (a b c : ZMod 4) : SL(2, ℤ) :=
  U ((c * a).val : ℤ) * (if a = 1 then 1 else -1) * E ((a * b).val : ℤ)

theorem map_liftFn_aux : ∀ a b c d : ZMod 4, a * d - b * c = 1 → IsUnit a →
    ((SLMOD(4) (liftFn a b c)) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![a, b; c, d] := by
  intro a b c d hdet hu
  have hmid : ((SLMOD(4) (if a = 1 then (1 : SL(2,ℤ)) else -1))
      : Matrix (Fin 2) (Fin 2) (ZMod 4)) = if a = 1 then !![1,0;0,1] else !![-1,0;0,-1] := by
    split_ifs with h
    · simp [Matrix.one_fin_two]
    · exact map_neg_one
  simp only [liftFn, map_mul, SpecialLinearGroup.coe_mul, map_U_val, map_E_val, hmid]
  split_ifs with h1 <;>
    · ext i j; fin_cases i <;> fin_cases j <;>
        · simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_fin_one, Matrix.empty_val']
          revert hdet hu h1; decide +revert

theorem mem_range_of_isUnit_00 (g : SpecialLinearGroup (Fin 2) (ZMod 4))
    (hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0)) :
    g ∈ (SLMOD(4)).range := by
  refine ⟨liftFn ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0), ?_⟩
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 1
      - (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 1
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0 = 1 := by
    have := g.2; rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [map_liftFn_aux _ _ _ _ hdet hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem SLMOD_four_surjective : Function.Surjective (SLMOD(4)) := by
  intro g
  rcases isUnit_col_of_det_one g with h0 | h1
  · exact (mem_range_of_isUnit_00 g h0)
  · have hSg : IsUnit (((SLMOD(4) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 4))
        : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0) := by
      have : ((SLMOD(4) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 4))
          : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0
          = - (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0 := by
        simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, ModularGroup.S]
        simp
      rw [this]; exact h1.neg
    obtain ⟨y, hy⟩ := mem_range_of_isUnit_00 _ hSg
    exact ⟨ModularGroup.S⁻¹ * y, by rw [map_mul, hy, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]⟩

theorem index_Gamma_four : (Gamma 4).index = 48 := by
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 4)) = 48 := by
    rw [Nat.card_eq_fintype_card]; exact card_SL2_ZMod_four
  rw [show Gamma 4 = (SLMOD(4)).ker from rfl, Subgroup.index_ker,
    (MonoidHom.range_eq_top).mpr SLMOD_four_surjective, ← hcard,
    Nat.card_congr (Subgroup.topEquiv).toEquiv]

end ModularCurve.PDPairing.IDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end Aux2IDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

section Aux2T1NAT

section Aux1BaseTwo

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace BaseTwo
p2m_open "ModularCurve.PDPairing ModularCurve"

open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup MulAction
open scoped MatrixGroups

abbrev red2 : SL(2, ℤ) →* SL(2, ZMod 2) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

theorem mem_Gamma_two_iff (g : SL(2, ℤ)) : g ∈ Gamma 2 ↔ red2 g = 1 := Gamma_mem'

def g₁ : SL(2, ℤ) := ⟨!![1, 0; -1, 1], by norm_num [Matrix.det_fin_two_of]⟩

def rep : Fin 3 → SL(2, ℤ) := ![1, S, g₁]

def ustd (i : Fin 3) : SL(2, ℤ) := (rep i)⁻¹ * T ^ (2 : ℕ) * rep i

theorem coe_ustd_zero : ((ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2; 0, 1] := by decide
theorem coe_ustd_one : ((ustd 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -2, 1] := by decide
theorem coe_ustd_two : ((ustd 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 2; -2, 3] := by decide

theorem red2_T_sq : red2 T ^ 2 = 1 := by decide

theorem red2_classify (x : SL(2, ZMod 2)) : ∃ j : Fin 2, ∃ i : Fin 3, x = red2 T ^ (j : ℕ) * red2 (rep i) := by
  revert x; decide

theorem red2_distinct (j : Fin 2) (i i' : Fin 3) (h : red2 T ^ (j : ℕ) * red2 (rep i) = red2 (rep i')) :
    i = i' ∧ j = 0 := by
  revert j i i' ; decide

theorem red2_ustd (i : Fin 3) : red2 (ustd i) = 1 := by revert i; decide

theorem red2_conj_T_ne (i : Fin 3) : red2 ((rep i)⁻¹ * T * rep i) ≠ 1 := by revert i; decide

theorem red2_T_zpow (j : ℤ) : ∃ j' : Fin 2, red2 (T ^ j) = red2 T ^ (j' : ℕ) := by
  have h2 : red2 T ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; exact red2_T_sq
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · refine ⟨0, ?_⟩
    rw [map_zpow, zpow_mul, h2, one_zpow]
    simp
  · refine ⟨1, ?_⟩
    rw [map_zpow, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    simp

theorem decomp (g : SL(2, ℤ)) : ∃ (i : Fin 3) (j : Fin 2) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ g = T ^ (j : ℕ) * rep i * γ := by
  obtain ⟨j, i, h⟩ := red2_classify (red2 g)
  refine ⟨i, j, (T ^ (j : ℕ) * rep i)⁻¹ * g, ?_, by group⟩
  rw [mem_Gamma_two_iff, map_mul, map_inv, map_mul, map_pow, ← h, inv_mul_cancel]

theorem decomp_unique {j j' : ℤ} {i i' : Fin 3} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) (hγ' : γ' ∈ Gamma 2)
    (h : T ^ j * rep i * γ = T ^ j' * rep i' * γ') : i = i' := by
  have h2 : T ^ (j - j') * rep i * (γ * γ'⁻¹) = rep i' := by
    calc T ^ (j - j') * rep i * (γ * γ'⁻¹) = (T ^ j')⁻¹ * (T ^ j * rep i * γ) * γ'⁻¹ := by group
      _ = rep i' := by rw [h]; group
  have hr := congrArg red2 h2
  obtain ⟨j₂, hj₂⟩ := red2_T_zpow (j - j')
  rw [map_mul, map_mul, (mem_Gamma_two_iff _).mp (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hγ')), mul_one,
    hj₂] at hr
  exact (red2_distinct j₂ i i' hr).1

section CuspDefs
variable (Φ : Subgroup SL(2, ℤ))

abbrev Cusp : Type := Quotient (orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Φ))

noncomputable scoped instance [Φ.FiniteIndex] : Fintype (Cusp Φ) := Fintype.ofFinite _

noncomputable def cuspGen (q : Cusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩
end CuspDefs
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

theorem iterate_smul_coe_eq_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) (n : ℕ) :
    (T • ·)^[n] ((g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Φ) = (g : SL(2, ℤ) ⧸ Φ) ↔ g⁻¹ * T ^ n * g ∈ Φ := by
  rw [smul_iterate_apply, Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, mul_inv_rev,
    show g⁻¹ * (T ^ n)⁻¹ * g = (g⁻¹ * T ^ n * g)⁻¹ by group, inv_mem_iff]

theorem conj_mem_iff_of_decomp (j : ℤ) (i : Fin 3) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) (n : ℕ) :
    (T ^ j * rep i * γ)⁻¹ * T ^ n * (T ^ j * rep i * γ) ∈ Gamma 2 ↔ (rep i)⁻¹ * T ^ n * rep i ∈ Gamma 2 := by
  rw [show (T ^ j * rep i * γ)⁻¹ * T ^ n * (T ^ j * rep i * γ) = γ⁻¹ * ((rep i)⁻¹ * T ^ n * rep i) * γ by group,
    Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hγ)]

theorem minimalPeriod_eq_two (j : ℤ) (i : Fin 3) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) :
    Function.minimalPeriod (T • ·) ((T ^ j * rep i * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Function.minimalPeriod_eq_prime
  · show (T • ·)^[2] _ = _
    rw [iterate_smul_coe_eq_iff, conj_mem_iff_of_decomp j i hγ, mem_Gamma_two_iff]
    exact red2_ustd i
  · show ¬ ((T • ·)^[1] _ = _)
    rw [iterate_smul_coe_eq_iff, conj_mem_iff_of_decomp j i hγ, mem_Gamma_two_iff, pow_one]
    exact red2_conj_T_ne i

theorem out_decomp (q : Cusp (Gamma 2)) :
    ∃ (i : Fin 3) (j : ℤ) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ q.out.out = T ^ j * rep i * γ := by
  obtain ⟨i, j, γ, hγ, h⟩ := decomp q.out.out
  exact ⟨i, j, γ, hγ, by rw [h, zpow_natCast]⟩

noncomputable def idx (q : Cusp (Gamma 2)) : Fin 3 := (out_decomp q).choose

theorem idx_spec (q : Cusp (Gamma 2)) :
    ∃ (j : ℤ) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ q.out.out = T ^ j * rep (idx q) * γ :=
  (out_decomp q).choose_spec

theorem cusp_eq_of_decomp (q : Cusp (Gamma 2)) {i : Fin 3} {j : ℤ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2)
    (h : q.out.out = T ^ j * rep i * γ) :
    q = Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) := by
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  show q.out ∈ MulAction.orbit (Subgroup.zpowers T) (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))
  rw [MulAction.mem_orbit_iff]
  refine ⟨⟨T ^ j, Subgroup.zpow_mem_zpowers T j⟩, ?_⟩
  rw [← QuotientGroup.out_eq' q.out, h]
  show ((T ^ j : SL(2, ℤ)) • (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))) = _
  rw [Quotient.smul_coe, smul_eq_mul]
  rw [QuotientGroup.eq, inv_mul_cancel_left]
  exact hγ

theorem idx_injective : Function.Injective idx := by
  intro q q' h
  obtain ⟨j, γ, hγ, hq⟩ := idx_spec q
  obtain ⟨j', γ', hγ', hq'⟩ := idx_spec q'
  rw [cusp_eq_of_decomp q hγ hq, cusp_eq_of_decomp q' hγ' hq', h]

theorem idx_mk (i : Fin 3) : idx (Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2)) = i := by
  set q : Cusp (Gamma 2) := Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) with hq
  obtain ⟨j, γ, hγ, h⟩ := idx_spec q

  have hmem : q.out ∈ MulAction.orbit (Subgroup.zpowers T) (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2)) := by
    have := Quotient.mk_out (s := orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Gamma 2))
      (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))
    exact this
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨⟨t, ht⟩, hts⟩ := hmem
  rw [Subgroup.mem_zpowers_iff] at ht
  obtain ⟨j₀, rfl⟩ := ht
  change ((T ^ j₀ : SL(2, ℤ)) • (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))) = _ at hts
  rw [Quotient.smul_coe, smul_eq_mul] at hts

  obtain ⟨⟨γ₀, hγ₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (Gamma 2) (T ^ j₀ * rep i)
  rw [hts] at hout

  have := decomp_unique hγ₀ hγ (hout.symm.trans h)
  exact this.symm

theorem idx_surjective : Function.Surjective idx := fun i => ⟨_, idx_mk i⟩

theorem Gamma_two_cusps :
    ∃ e : Cusp (Gamma 2) ≃ Fin 3, ∀ q : Cusp (Gamma 2), ∃ γ : SL(2, ℤ), γ ∈ Gamma 2 ∧
      ((cuspGen (Gamma 2) q : Gamma 2) : SL(2, ℤ)) = γ⁻¹ * ustd (e q) * γ := by
  refine ⟨Equiv.ofBijective idx ⟨idx_injective, idx_surjective⟩, fun q => ?_⟩
  obtain ⟨j, γ, hγ, h⟩ := idx_spec q
  refine ⟨γ, hγ, ?_⟩
  show q.out.out⁻¹ * T ^ Function.minimalPeriod (T • ·) q.out * q.out.out = γ⁻¹ * ustd (idx q) * γ
  have hper : Function.minimalPeriod (T • ·) q.out = 2 := by
    rw [← QuotientGroup.out_eq' q.out, h]
    exact minimalPeriod_eq_two j (idx q) hγ
  rw [hper, h, ustd]
  group

end ModularCurve.PDPairing.BaseTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier"

end Aux1BaseTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace T1
p2m_open "ModularCurve.PDPairing ModularCurve"

open Function MulAction Subgroup ModularCurve.PDPairing.CuspTower

variable {G : Type*} [Group G] {K' K : Subgroup G}

noncomputable scoped instance instFintypeACusp (g : G) (H : Subgroup G) [H.FiniteIndex] :
    Fintype (ACusp g H) := by
  haveI : Finite (G ⧸ H) := H.finite_quotient_of_finiteIndex
  exact Fintype.ofFinite _

variable {A : Type*} [CommGroup A]

theorem map_conj_eq (ϕ : K' →* A) (c v : K') : ϕ (c * v * c⁻¹) = ϕ v := by
  rw [map_mul, map_mul, map_inv, mul_comm (ϕ c), mul_assoc, mul_inv_cancel, mul_one]

noncomputable def innerSummand (g : G) (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ↥K' :=
  Subgroup.subgroupOfEquivOfLe hle
    ⟨o.out.out⁻¹ * (acuspGen g K q) ^ minimalPeriod ((acuspGen g K q) • ·) o.out * o.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem (K'.subgroupOf K) (acuspGen g K q) o.out⟩

theorem innerSummand_coe (g : G) (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ((innerSummand g hle q o : K') : G)
      = ((o.out.out : K) : G)⁻¹ * ((acuspGen g K q : K) : G) ^
          minimalPeriod ((acuspGen g K q) • ·) o.out * ((o.out.out : K) : G) := by
  simp [innerSummand, Subgroup.subgroupOfEquivOfLe]

theorem transfer_eq_prod_sigma (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) :
    MonoidHom.transfer ϕ g = ∏ q : ACusp g K, ∏ o : InnerOrbit g K' K hle q,
      ϕ (innerSummand g hle q o) := by
  haveI : Finite (G ⧸ K) := K.finite_quotient_of_finiteIndex
  haveI : ∀ q : ACusp g K, Fintype (InnerOrbit g K' K hle q) := fun q => by
    haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
    exact Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    ← Equiv.prod_comp (towerEquiv g hle)]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr (by congr 1) fun q _ => ?_
  refine Finset.prod_congr (by congr 1; exact Subsingleton.elim _ _) fun o _ => ?_
  obtain ⟨c', hc'⟩ := acuspGen_towerEquiv_conj g hle q o
  rw [← map_conj_eq ϕ c' (innerSummand g hle q o)]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, innerSummand_coe]
  exact hc'

theorem prod_innerSummand_eq_transfer (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) (q : ACusp g K) :
    haveI : Fintype (InnerOrbit g K' K hle q) := by
      haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
      exact Fintype.ofFinite _
    ∏ o : InnerOrbit g K' K hle q, ϕ (innerSummand g hle q o)
      = MonoidHom.transfer
          (ϕ.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
          (acuspGen g K q) := by
  haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
  haveI : Fintype (InnerOrbit g K' K hle q) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr ?_ fun o _ => rfl
  congr 1
  exact Subsingleton.elim _ _

theorem transfer_transfer (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) :
    MonoidHom.transfer
      (MonoidHom.transfer (ϕ.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) : K →* A) g
    = MonoidHom.transfer ϕ g := by
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
    (H := K) (ϕ := MonoidHom.transfer _) g,
    transfer_eq_prod_sigma g hle ϕ]
  refine Finset.prod_congr (by congr 1) fun q _ =>
    (prod_innerSummand_eq_transfer g hle ϕ q).symm

section NAT

variable {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂] (σ : G₁ ≃* G₂) (L : Subgroup G₂)

def quotCongr : G₁ ⧸ (L.comap σ.toMonoidHom) ≃ G₂ ⧸ L :=
  Quotient.congr σ.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_comap,
      map_mul, map_inv]; rfl

@[scoped simp] theorem quotCongr_mk (a : G₁) :
    quotCongr σ L (QuotientGroup.mk a) = QuotientGroup.mk (σ a) := rfl

theorem quotCongr_smul (h : G₁) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    quotCongr σ L (h • x) = (σ h) • (quotCongr σ L x) := by
  refine x.induction_on fun a => ?_
  show QuotientGroup.mk (s := L) (σ (h * a)) = (σ h) • QuotientGroup.mk (s := L) (σ a)
  rw [map_mul]; rfl

theorem quotCongr_zpow_smul (h : G₁) (n : ℤ) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    quotCongr σ L (h ^ n • x) = (σ h) ^ n • (quotCongr σ L x) := by
  rw [quotCongr_smul, map_zpow]

theorem minimalPeriod_quotCongr (h : G₁) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    minimalPeriod ((σ h) • ·) (quotCongr σ L x) = minimalPeriod (h • ·) x := by
  have hiter : ∀ n : ℕ, (σ h) ^ n • (quotCongr σ L x) = quotCongr σ L (h ^ n • x) := fun n => by
    rw [← map_pow, ← quotCongr_smul]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hiter]; exact congrArg _ ((pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl)
  · have h' := (pow_smul_eq_iff_minimalPeriod_dvd (a := σ h) (b := quotCongr σ L x)
      (n := minimalPeriod ((σ h) • ·) (quotCongr σ L x))).mpr dvd_rfl
    rw [hiter] at h'; exact (quotCongr σ L).injective h'

def acuspCongr (h : G₁) : ACusp h (L.comap σ.toMonoidHom) ≃ ACusp (σ h) L :=
  Quotient.congr (quotCongr σ L) fun a b => by
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨hh, hn⟩
      obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
      have hn' : h ^ n • b = a := hng ▸ hn
      exact ⟨⟨(σ h) ^ n, n, rfl⟩, by
        show (σ h) ^ n • (quotCongr σ L b) = quotCongr σ L a
        rw [← quotCongr_zpow_smul]; exact congrArg _ hn'⟩
    · rintro ⟨hh, hn⟩
      obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
      have hn' : (σ h) ^ n • (quotCongr σ L b) = quotCongr σ L a := hng ▸ hn
      refine ⟨⟨h ^ n, n, rfl⟩, (quotCongr σ L).injective ?_⟩
      show quotCongr σ L (h ^ n • b) = quotCongr σ L a
      rw [quotCongr_zpow_smul]; exact hn'

theorem acuspGen_acuspCongr_conj [L.FiniteIndex]
    [(L.comap σ.toMonoidHom).FiniteIndex] (h : G₁) (q' : ACusp h (L.comap σ.toMonoidHom)) :
    ∃ l : L, ((acuspGen (σ h) L (acuspCongr σ L h q') : L) : G₂)
      = (l : G₂)
        * (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q') : G₂)
        * (l : G₂)⁻¹ := by
  haveI : Finite (G₂ ⧸ L) := L.finite_quotient_of_finiteIndex
  set q := acuspCongr σ L h q' with hq

  have hqc : quotCongr σ L q'.out = QuotientGroup.mk (s := L) (σ q'.out.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q'.out]
    rfl
  have hqmk : q = Quotient.mk _ (quotCongr σ L q'.out) := by
    conv_lhs => rw [hq, ← Quotient.out_eq q', show acuspCongr σ L h ⟦q'.out⟧
      = ⟦quotCongr σ L q'.out⟧ from rfl]
  have horb : (Quotient.mk _ q.out : ACusp (σ h) L)
      = Quotient.mk _ (quotCongr σ L q'.out) := by rw [Quotient.out_eq]; exact hqmk
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at horb
  obtain ⟨hh, hn⟩ := horb
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
  have hn' : (σ h) ^ n • (quotCongr σ L q'.out) = q.out := hng ▸ hn
  clear hng hn hh
  rw [hqc] at hn'

  have hl : q.out.out⁻¹ * ((σ h) ^ n * σ (q'.out.out)) ∈ L := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']; exact hn'.symm
  refine ⟨⟨_, hl⟩, ?_⟩
  have hm' : minimalPeriod ((σ h) • ·) q.out = minimalPeriod (h • ·) q'.out := by
    rw [← hn']; conv_lhs => rw [← hqc]
    rw [← quotCongr_zpow_smul, minimalPeriod_quotCongr, minimalPeriod_zpow_smul]
  have hscoe : (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q') : G₂)
      = (σ (q'.out.out))⁻¹ * (σ h) ^ minimalPeriod (h • ·) q'.out * σ (q'.out.out) := by
    show σ _ = _; simp only [acuspGen, map_mul, map_inv, map_pow]
  show q.out.out⁻¹ * (σ h) ^ minimalPeriod ((σ h) • ·) q.out * q.out.out = _
  rw [hm', hscoe, Subgroup.coe_mk]

  group

scoped instance finiteIndex_comap_mulEquiv [hL : L.FiniteIndex] :
    (L.comap σ.toMonoidHom).FiniteIndex :=
  ⟨by rw [L.index_comap_of_surjective σ.surjective]; exact hL.1⟩

theorem transfer_congr [L.FiniteIndex] (χ : ↥L →* A) (h : G₁) :
    MonoidHom.transfer χ (σ h) = MonoidHom.transfer (χ.comp (σ.toMonoidHom.subgroupComap L)) h := by
  haveI : Finite (G₁ ⧸ L.comap σ.toMonoidHom) := (L.comap σ.toMonoidHom).finite_quotient_of_finiteIndex
  haveI : Fintype (ACusp h (L.comap σ.toMonoidHom)) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot (ϕ := χ) (σ h),
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
      (ϕ := χ.comp (σ.toMonoidHom.subgroupComap L)) h,
    ← Equiv.prod_comp (acuspCongr σ L h)]
  refine Finset.prod_congr (by congr 1) fun q' _ => ?_
  obtain ⟨l, hlconj⟩ := acuspGen_acuspCongr_conj σ L h q'
  have heq : acuspGen (σ h) L (acuspCongr σ L h q')
      = l * (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q')) * l⁻¹ := by
    apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hlconj]
  show χ (acuspGen (σ h) L (acuspCongr σ L h q')) = _
  rw [heq, map_conj_eq χ l, MonoidHom.comp_apply]
  rfl

end NAT
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"

section CoresCores

variable {G : Type*} [Group G] {K H G' : Subgroup G}
variable {R : Type*} [CommRing R]

noncomputable def cores {Φ' Φ : Subgroup G} (h : Φ' ≤ Φ) [Φ'.FiniteIndex]
    (x : Additive Φ' →+ R) : Additive Φ →+ R :=
  MonoidHom.toAdditiveLeft
    (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom))))

theorem subgroupOf_subgroupOf_eq_comap (hHG : H ≤ G') :
    (K.subgroupOf G').subgroupOf (H.subgroupOf G')
      = (K.subgroupOf H).comap (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom := by
  ext x; rfl

scoped instance finiteIndex_comap_equiv (hHG : H ≤ G') (L : Subgroup ↥H) [hL : L.FiniteIndex] :
    (L.comap (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom).FiniteIndex :=
  ⟨by rw [L.index_comap_of_surjective (Subgroup.subgroupOfEquivOfLe hHG).surjective]; exact hL.1⟩

theorem transfer_congr_subgroupOf (hHG : H ≤ G') (L : Subgroup ↥H) [L.FiniteIndex]
    (χ : ↥L →* A) (h : ↥(H.subgroupOf G')) :
    MonoidHom.transfer χ ((Subgroup.subgroupOfEquivOfLe hHG) h)
      = MonoidHom.transfer
          (χ.comp ((Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom.subgroupComap L)) h :=
  transfer_congr (Subgroup.subgroupOfEquivOfLe hHG) L χ h

theorem equiv_comp_coe (hKH : K ≤ H) (hHG : H ≤ G')
    (w : ↥((K.subgroupOf G').subgroupOf (H.subgroupOf G'))) :
    ((Subgroup.subgroupOfEquivOfLe (hKH.trans hHG))
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.subgroupOf_mono G' hKH)) w) : G)
    = ((Subgroup.subgroupOfEquivOfLe hKH)
        (((Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom.subgroupComap (K.subgroupOf H))
          (MulEquiv.subgroupCongr (subgroupOf_subgroupOf_eq_comap hHG) w)) : G) := rfl

theorem cores_cores (hKH : K ≤ H) (hHG : H ≤ G') [K.FiniteIndex] [H.FiniteIndex]
    (x : Additive K →+ R) :
    cores hHG (cores hKH x) = cores (hKH.trans hHG) x := by
  have hle : K.subgroupOf G' ≤ H.subgroupOf G' := Subgroup.subgroupOf_mono G' hKH
  have hchareq :
      (AddMonoidHom.toMultiplicativeRight
        ((cores hKH x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom)))
      = MonoidHom.transfer
          ((AddMonoidHom.toMultiplicativeRight
              (x.comp (MonoidHom.toAdditive
                (Subgroup.subgroupOfEquivOfLe (hKH.trans hHG)).toMonoidHom))).comp
            (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) := by

    ext hh

    set χ := AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom))
    show MonoidHom.transfer χ ((Subgroup.subgroupOfEquivOfLe hHG) hh) = _
    rw [transfer_congr_subgroupOf hHG (K.subgroupOf H) χ hh]

    congr 1
  have h := transfer_transfer (G := ↥G') (K' := K.subgroupOf G') (K := H.subgroupOf G')
    (A := Multiplicative R)
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer
      (AddMonoidHom.toMultiplicativeRight
        ((cores hKH x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom))))
    = MonoidHom.toAdditiveLeft (MonoidHom.transfer
        (AddMonoidHom.toMultiplicativeRight
          (x.comp (MonoidHom.toAdditive
            (Subgroup.subgroupOfEquivOfLe (hKH.trans hHG)).toMonoidHom))))
  rw [hchareq]
  exact congrArg _ (MonoidHom.ext fun g' => h g' hle _)

end CoresCores
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"

end ModularCurve.PDPairing.T1
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo"

end Aux2T1NAT
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace TD
p2m_open "ModularCurve.PDPairing ModularCurve"

section Prim

variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

variable [IsFreeGroup Φ]

theorem hPrim_mul_of_omega_eq_zero (φ ψ : Additive Φ →+ R) (g g' : Φ) (h0 : omega φ ψ g g' = 0) :
    hPrim φ ψ (g * g') = hPrim φ ψ g + hPrim φ ψ g' := by
  rw [hPrim_mul, h0, sub_zero]

theorem hPrim_inv (φ ψ : Additive Φ →+ R) (g : Φ) : hPrim φ ψ g⁻¹ = - hPrim φ ψ g := by
  have h := hPrim_mul φ ψ g g⁻¹
  rw [mul_inv_cancel, hPrim_one, omega_self_inv, sub_zero] at h
  linear_combination -h

omit [IsFreeGroup Φ] in
theorem omega_inv_right (φ ψ : Additive Φ →+ R) (u g : Φ) : omega φ ψ u g⁻¹ = - omega φ ψ u g := by
  simp only [omega, ofMul_inv, map_neg]
  ring

omit [IsFreeGroup Φ] in
theorem omega_conj_aux (φ ψ : Additive Φ →+ R) (g u : Φ) :
    omega φ ψ g (u * g⁻¹) = - omega φ ψ u g := by
  simp only [omega, ofMul_mul, ofMul_inv, map_add, map_neg]
  ring

theorem hPrim_conj (φ ψ : Additive Φ →+ R) (g u : Φ) :
    hPrim φ ψ (g * u * g⁻¹) = hPrim φ ψ u + 2 * omega φ ψ u g := by
  rw [mul_assoc, hPrim_mul, hPrim_mul, hPrim_inv, omega_conj_aux, omega_inv_right]
  ring

omit [IsFreeGroup Φ] in
theorem omega_eq_zero_of_apply_eq_zero (φ ψ : Additive Φ →+ R) (u : Φ) (hφ : φ (Additive.ofMul u) = 0)
    (hψ : ψ (Additive.ofMul u) = 0) (g : Φ) : omega φ ψ u g = 0 := by
  simp [omega, hφ, hψ]

theorem hPrim_conj_of_apply_eq_zero (φ ψ : Additive Φ →+ R) (u : Φ) (hφ : φ (Additive.ofMul u) = 0)
    (hψ : ψ (Additive.ofMul u) = 0) (g : Φ) : hPrim φ ψ (g * u * g⁻¹) = hPrim φ ψ u := by
  rw [hPrim_conj, omega_eq_zero_of_apply_eq_zero φ ψ u hφ hψ g, mul_zero, add_zero]

omit [IsFreeGroup Φ] in
theorem omega_pow_self (φ ψ : Additive Φ →+ R) (u : Φ) (k : ℕ) : omega φ ψ (u ^ k) u = 0 := by
  simp only [omega, ofMul_pow, map_nsmul, nsmul_eq_mul]
  ring

theorem hPrim_pow (φ ψ : Additive Φ →+ R) (u : Φ) (k : ℕ) : hPrim φ ψ (u ^ k) = k * hPrim φ ψ u := by
  induction k with
  | zero => simp [hPrim_one]
  | succ k ih =>
    rw [pow_succ, hPrim_mul, ih, omega_pow_self]
    push_cast
    ring

theorem hPrim_of (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a) = 0 := by
  show (sect φ ψ (IsFreeGroup.of a)).1 = 0
  simp [sect]

theorem hPrim_of_inv (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a)⁻¹ = 0 := by
  rw [hPrim_inv, hPrim_of, neg_zero]

omit [IsFreeGroup Φ] in
theorem omega_one_right' (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g 1 = 0 := by
  simp [omega]

omit [IsFreeGroup Φ] in
theorem omega_mul_right' (φ ψ : Additive Φ →+ R) (g a b : Φ) :
    omega φ ψ g (a * b) = omega φ ψ g a + omega φ ψ g b := by
  simp only [omega, ofMul_mul, map_add]
  ring

def pairSum (φ ψ : Additive Φ →+ R) : List Φ → R
  | [] => 0
  | g :: L => (L.map (omega φ ψ g)).sum + pairSum φ ψ L

omit [IsFreeGroup Φ] in
theorem omega_list_prod (φ ψ : Additive Φ →+ R) (g : Φ) (L : List Φ) :
    omega φ ψ g L.prod = (L.map (omega φ ψ g)).sum := by
  induction L with
  | nil => rw [List.prod_nil, omega_one_right', List.map_nil, List.sum_nil]
  | cons a L ih => rw [List.prod_cons, omega_mul_right', ih, List.map_cons, List.sum_cons]

theorem hPrim_list_prod (φ ψ : Additive Φ →+ R) (L : List Φ) (hL : ∀ g ∈ L, hPrim φ ψ g = 0) :
    hPrim φ ψ L.prod = - pairSum φ ψ L := by
  induction L with
  | nil => rw [List.prod_nil, hPrim_one, pairSum, neg_zero]
  | cons g L ih =>
    rw [List.prod_cons, hPrim_mul, hL g (by simp), ih (fun g' hg' => hL g' (by simp [hg'])), omega_list_prod,
      pairSum]
    ring

theorem hPrim_list_prod' (φ ψ : Additive Φ →+ R) (L : List Φ) :
    hPrim φ ψ L.prod = (L.map (hPrim φ ψ)).sum - pairSum φ ψ L := by
  induction L with
  | nil => rw [List.prod_nil, hPrim_one, pairSum, List.map_nil, List.sum_nil, sub_zero]
  | cons g L ih =>
    rw [List.prod_cons, hPrim_mul, ih, omega_list_prod, pairSum, List.map_cons, List.sum_cons]
    ring

end Prim
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

section Orientation

def orientForm (N : Matrix (Fin 2) (Fin 2) ℤ) (y0 y1 : ℤ) : ℤ :=
  N 1 0 * y0 ^ 2 + (N 1 1 - N 0 0) * y0 * y1 - N 0 1 * y1 ^ 2

theorem orientForm_intertwine (a M N : Matrix (Fin 2) (Fin 2) ℤ) (h : M * a = a * N) (y0 y1 : ℤ) :
    orientForm M (a 0 0 * y0 + a 0 1 * y1) (a 1 0 * y0 + a 1 1 * y1) = a.det * orientForm N y0 y1 := by
  have e := fun i j => congrFun (congrFun h i) j
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  simp only [orientForm, Matrix.det_fin_two]
  linear_combination (-(a 1 0 * y0 + a 1 1 * y1) * y0) * h00 + (-(a 1 0 * y0 + a 1 1 * y1) * y1) * h01
    + ((a 0 0 * y0 + a 0 1 * y1) * y0) * h10 + ((a 0 0 * y0 + a 0 1 * y1) * y1) * h11

def IsPosUnipotent (u : Matrix (Fin 2) (Fin 2) ℤ) : Prop := 0 < u 0 1 ∨ (u 0 1 = 0 ∧ u 1 0 < 0)

theorem orientForm_neg_iff (u : Matrix (Fin 2) (Fin 2) ℤ) (htr : u.trace = 2) (hdet : u.det = 1)
    (y0 y1 : ℤ) (hy : (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 ∨ u 1 0 * y0 + (u 1 1 - 1) * y1 ≠ 0) :
    orientForm (u - 1) y0 y1 < 0 ↔ IsPosUnipotent u := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have hαδ : (u 0 0 - 1) + (u 1 1 - 1) = 0 := by linear_combination htr
  have hN : (u 0 0 - 1) * (u 1 1 - 1) - u 0 1 * u 1 0 = 0 := by linear_combination hdet - htr
  have hform : orientForm (u - 1) y0 y1 =
      u 1 0 * y0 ^ 2 + ((u 1 1 - 1) - (u 0 0 - 1)) * y0 * y1 - u 0 1 * y1 ^ 2 := by
    simp [orientForm, Matrix.sub_apply]
  rw [hform]
  by_cases hb : u 0 1 = 0
  ·
    have hα2 : (u 0 0 - 1) ^ 2 = 0 := by
      linear_combination (u 0 0 - 1) * hαδ - hN + (- u 1 0) * hb
    have hα : u 0 0 - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hα2
    have hδ : u 1 1 - 1 = 0 := by linear_combination hαδ - hα
    have hy' : u 1 0 * y0 ≠ 0 := by
      rcases hy with hy | hy
      · exfalso; apply hy; rw [hα, hb]; ring
      · rwa [hδ, zero_mul, add_zero] at hy
    have hγ : u 1 0 ≠ 0 := left_ne_zero_of_mul hy'
    have hy0 : y0 ≠ 0 := right_ne_zero_of_mul hy'
    have hy0sq : 0 < y0 ^ 2 := lt_of_le_of_ne (sq_nonneg y0) (Ne.symm (pow_ne_zero 2 hy0))
    simp only [IsPosUnipotent, hb, lt_self_iff_false, false_or, true_and]
    rw [hα, hδ]
    constructor
    · intro h; nlinarith [hy0sq, h]
    · intro h; nlinarith [hy0sq, h]
  ·
    have ht : (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 := by
      rcases hy with hy | hy
      · exact hy
      · intro h0
        apply hy

        have : u 0 1 * (u 1 0 * y0 + (u 1 1 - 1) * y1) = 0 := by
          linear_combination (-y0) * hN + (u 1 1 - 1) * h0
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hb
        · exact h'
    have htsq : 0 < ((u 0 0 - 1) * y0 + u 0 1 * y1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ht))
    have key : u 0 1 * (u 1 0 * y0 ^ 2 + ((u 1 1 - 1) - (u 0 0 - 1)) * y0 * y1 - u 0 1 * y1 ^ 2) =
        - ((u 0 0 - 1) * y0 + u 0 1 * y1) ^ 2 := by
      linear_combination (-(y0 ^ 2)) * hN + ((u 0 0 - 1) * y0 ^ 2 + u 0 1 * y0 * y1) * hαδ
    simp only [IsPosUnipotent, hb, false_and, or_false]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

theorem isPosUnipotent_intertwine (a u u'' : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (h : u'' * a = a * u) (htr : u.trace = 2) (hdet : u.det = 1) (htr'' : u''.trace = 2)
    (hdet'' : u''.det = 1) (hu : u ≠ 1) : IsPosUnipotent u ↔ IsPosUnipotent u'' := by

  have hex : ∃ y0 y1 : ℤ, (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 ∨ u 1 0 * y0 + (u 1 1 - 1) * y1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu
    have e0 := hcon 1 0
    have e1 := hcon 0 1
    simp only [mul_one, mul_zero, add_zero, zero_add] at e0 e1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination e0.1
    · linear_combination e1.1
    · linear_combination e0.2
    · linear_combination e1.2
  obtain ⟨y0, y1, hy⟩ := hex

  have hN : (u'' - 1) * a = a * (u - 1) := by rw [sub_mul, mul_sub, one_mul, mul_one, h]
  have hcov := orientForm_intertwine a (u'' - 1) (u - 1) hN y0 y1

  have hy'' : ((u'' 0 0 - 1) * (a 0 0 * y0 + a 0 1 * y1) + u'' 0 1 * (a 1 0 * y0 + a 1 1 * y1) ≠ 0 ∨
      u'' 1 0 * (a 0 0 * y0 + a 0 1 * y1) + (u'' 1 1 - 1) * (a 1 0 * y0 + a 1 1 * y1) ≠ 0) := by
    have e := fun i j => congrFun (congrFun hN i) j
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] at h00 h01 h10 h11
    simp only [Fin.isValue, ↓reduceIte, OfNat.ofNat_ne_one, Fin.zero_eq_one_iff,
      one_ne_zero, sub_zero] at h00 h01 h10 h11

    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1⟩ := hcon
    set w0 := (u 0 0 - 1) * y0 + u 0 1 * y1 with hw0
    set w1 := u 1 0 * y0 + (u 1 1 - 1) * y1 with hw1
    have k0 : a 0 0 * w0 + a 0 1 * w1 = 0 := by
      rw [hw0, hw1]; linear_combination c0 - y0 * h00 - y1 * h01
    have k1 : a 1 0 * w0 + a 1 1 * w1 = 0 := by
      rw [hw0, hw1]; linear_combination c1 - y0 * h10 - y1 * h11
    have hd : a.det ≠ 0 := ne_of_gt ha
    rw [Matrix.det_fin_two] at hd
    have hw0z : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * w0 = 0 := by
      linear_combination a 1 1 * k0 - a 0 1 * k1
    have hw1z : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * w1 = 0 := by
      linear_combination a 0 0 * k1 - a 1 0 * k0
    rcases hy with hy | hy
    · exact hy ((mul_eq_zero.mp hw0z).resolve_left hd)
    · exact hy ((mul_eq_zero.mp hw1z).resolve_left hd)
  rw [← orientForm_neg_iff u htr hdet y0 y1 hy, ← orientForm_neg_iff u'' htr'' hdet'' _ _ hy'', hcov]
  constructor
  · intro hneg; exact mul_neg_of_pos_of_neg ha hneg
  · intro hneg
    by_contra hcon
    push Not at hcon
    have : 0 ≤ a.det * orientForm (u - 1) y0 y1 := mul_nonneg ha.le hcon
    exact absurd hneg (not_lt.mpr this)

end Orientation
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

section CoresPrimitive

open MulAction

variable {G : Type*} [Group G] (K : Subgroup G) [Fintype (G ⧸ K)] {R : Type*} [CommRing R]
variable (sec : G ⧸ K → G) (hsec : ∀ q : G ⧸ K, (sec q : G ⧸ K) = q)

include hsec in
omit [Fintype (G ⧸ K)] in
theorem gamma_mem (q : G ⧸ K) (g : G) : (sec q)⁻¹ * g * sec (g⁻¹ • q) ∈ K := by
  have h : ((sec q : G) : G ⧸ K) = ((g * sec (g⁻¹ • q) : G) : G ⧸ K) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, hsec, hsec, smul_inv_smul]
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

def gam (q : G ⧸ K) (g : G) : K := ⟨(sec q)⁻¹ * g * sec (g⁻¹ • q), gamma_mem K sec hsec q g⟩

omit [Fintype (G ⧸ K)] in
@[scoped simp] theorem coe_gam (q : G ⧸ K) (g : G) :
    ((gam K sec hsec q g : K) : G) = (sec q)⁻¹ * g * sec (g⁻¹ • q) := rfl

omit [Fintype (G ⧸ K)] in

theorem gam_mul (q : G ⧸ K) (g g' : G) :
    gam K sec hsec q (g * g') = gam K sec hsec q g * gam K sec hsec (g⁻¹ • q) g' := by
  apply Subtype.ext
  simp only [coe_gam, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

def coresFun (x : Additive K →+ R) (g : G) : R := ∑ q : G ⧸ K, x (Additive.ofMul (gam K sec hsec q g))

def HFun (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R) (g : G) : R :=
  ∑ q : G ⧸ K, (h' (gam K sec hsec q g) +
    x (Additive.ofMul (gam K sec hsec q g)) * (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q))))

theorem HFun_mul (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (g g' : G) :
    HFun K sec hsec h' x y (g * g') = HFun K sec hsec h' x y g + HFun K sec hsec h' x y g' -
      (coresFun K sec hsec x g * y (Additive.ofMul g') - y (Additive.ofMul g) * coresFun K sec hsec x g') := by

  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹
  have e1 : HFun K sec hsec h' x y g' = ∑ q : G ⧸ K, (h' (gam K sec hsec (g⁻¹ • q) g') +
      x (Additive.ofMul (gam K sec hsec (g⁻¹ • q) g')) *
        (y (Additive.ofMul (sec (g'⁻¹ • g⁻¹ • q))) + y (Additive.ofMul (sec (g⁻¹ • q))))) := by
    rw [HFun]
    exact (hb.sum_comp (fun q => h' (gam K sec hsec q g') +
      x (Additive.ofMul (gam K sec hsec q g')) *
        (y (Additive.ofMul (sec (g'⁻¹ • q))) + y (Additive.ofMul (sec q))))).symm
  have e2 : coresFun K sec hsec x g' = ∑ q : G ⧸ K, x (Additive.ofMul (gam K sec hsec (g⁻¹ • q) g')) := by
    rw [coresFun]
    exact (hb.sum_comp (fun q => x (Additive.ofMul (gam K sec hsec q g')))).symm
  rw [e1, e2]
  simp only [HFun, coresFun]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)

  rw [gam_mul, hh', ofMul_mul, map_add, mul_inv_rev, mul_smul]

  have y1 : y (Additive.ofMul ((gam K sec hsec q g : K) : G)) =
      - y (Additive.ofMul (sec q)) + y (Additive.ofMul g) + y (Additive.ofMul (sec (g⁻¹ • q))) := by
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  have y2 : y (Additive.ofMul ((gam K sec hsec (g⁻¹ • q) g' : K) : G)) =
      - y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul g') +
        y (Additive.ofMul (sec (g'⁻¹ • g⁻¹ • q))) := by
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [y1, y2]
  ring

theorem coresFun_eq [K.FiniteIndex] (x : Additive K →+ R) (g : G) :
    coresFun K sec hsec x g =
      Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight x) g) := by
  classical
  let T : K.LeftTransversal := ⟨Set.range sec, Subgroup.isComplement_range_left hsec⟩
  rw [MonoidHom.transfer_def _ T g, Subgroup.leftTransversals.diff, toAdd_prod, coresFun]
  have hinst : (K.fintypeQuotientOfFiniteIndex : Fintype (G ⧸ K)) = ‹Fintype (G ⧸ K)› :=
    Subsingleton.elim _ _
  rw [hinst]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [AddMonoidHom.coe_toMultiplicativeRight]
  simp only [Function.comp_apply, toAdd_ofAdd]
  congr 1
  congr 1
  apply Subtype.ext
  simp only [coe_gam]
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul g T q, smul_eq_mul,
    Subgroup.IsComplement.leftQuotientEquiv_apply hsec, Subgroup.IsComplement.leftQuotientEquiv_apply hsec,
    mul_assoc]

include hsec in
omit [Fintype (G ⧸ K)] in
theorem secChange_mem (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) :
    (sec q)⁻¹ * sec' q ∈ K := by
  have h : ((sec q : G) : G ⧸ K) = ((sec' q : G) : G ⧸ K) := by rw [hsec, hsec']
  exact QuotientGroup.eq.mp h

def kSec (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) : K :=
  ⟨(sec q)⁻¹ * sec' q, secChange_mem K sec hsec sec' hsec' q⟩

omit [Fintype (G ⧸ K)] in
@[scoped simp] theorem coe_kSec (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) :
    ((kSec K sec hsec sec' hsec' q : K) : G) = (sec q)⁻¹ * sec' q := rfl

omit [Fintype (G ⧸ K)] in
theorem gam_secChange (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K)
    (g : G) :
    gam K sec' hsec' q g =
      (kSec K sec hsec sec' hsec' q)⁻¹ * gam K sec hsec q g * kSec K sec hsec sec' hsec' (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [coe_gam, Subgroup.coe_mul, Subgroup.coe_inv, coe_kSec, mul_inv_rev, inv_inv]
  group

theorem HFun_secChange (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q)
    (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (g : G) :
    HFun K sec' hsec' h' x y g = HFun K sec hsec h' x y g +
      2 * y (Additive.ofMul g) * ∑ q : G ⧸ K, x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) := by
  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹

  have h1 : h' 1 = 0 := by
    have h := hh' 1 1
    simp only [mul_one, ofMul_one, map_zero, OneMemClass.coe_one, mul_zero, sub_zero, sub_self] at h
    linear_combination -h
  have hinv : ∀ k : K, h' k⁻¹ = - h' k := by
    intro k
    have h := hh' k k⁻¹
    simp only [mul_inv_cancel, h1, ofMul_inv, map_neg, Subgroup.coe_inv, mul_neg,
      sub_neg_eq_add] at h
    linear_combination -h

  set D : G ⧸ K → R := fun q => x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) *
      y (Additive.ofMul ((kSec K sec hsec sec' hsec' q : K) : G)) +
      2 * y (Additive.ofMul (sec q)) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
      h' (kSec K sec hsec sec' hsec' q) with hD
  have hDsum : ∑ q : G ⧸ K, D (g⁻¹ • q) = ∑ q : G ⧸ K, D q := hb.sum_comp D
  have hκsum : ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) =
      ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) :=
    hb.sum_comp (fun q => y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)))

  have hpt : ∀ q : G ⧸ K,
      (h' (gam K sec' hsec' q g) + x (Additive.ofMul (gam K sec' hsec' q g)) *
          (y (Additive.ofMul (sec' (g⁻¹ • q))) + y (Additive.ofMul (sec' q)))) =
      (h' (gam K sec hsec q g) + x (Additive.ofMul (gam K sec hsec q g)) *
          (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q)))) +
        (y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (D (g⁻¹ • q) - D q)) := by
    intro q
    have hs' : ∀ q, y (Additive.ofMul (sec' q)) =
        y (Additive.ofMul (sec q)) + y (Additive.ofMul ((kSec K sec hsec sec' hsec' q : K) : G)) := by
      intro q
      rw [← map_add, ← ofMul_mul, coe_kSec, mul_inv_cancel_left]
    have hyγ : y (Additive.ofMul ((gam K sec hsec q g : K) : G)) =
        - y (Additive.ofMul (sec q)) + y (Additive.ofMul g) + y (Additive.ofMul (sec (g⁻¹ • q))) := by
      simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
    rw [gam_secChange K sec hsec sec' hsec' q g, hh', hh', hinv, hs' q, hs' (g⁻¹ • q)]
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg, Subgroup.coe_mul, Subgroup.coe_inv, hyγ, hD]
    ring
  calc HFun K sec' hsec' h' x y g
      = ∑ q : G ⧸ K, ((h' (gam K sec hsec q g) + x (Additive.ofMul (gam K sec hsec q g)) *
          (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q)))) +
        (y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (D (g⁻¹ • q) - D q))) := by
        rw [HFun]
        exact Finset.sum_congr rfl (fun q _ => hpt q)
    _ = HFun K sec hsec h' x y g +
        (∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (∑ q : G ⧸ K, D (g⁻¹ • q) - ∑ q : G ⧸ K, D q)) := by
        rw [HFun]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = HFun K sec hsec h' x y g +
        2 * y (Additive.ofMul g) * ∑ q : G ⧸ K, x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) := by
        rw [hDsum, hκsum, sub_self, add_zero, ← two_mul, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]

theorem HFun_transferFunction_eq [K.FiniteIndex] (u : G)
    [Fintype (Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))]
    (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (hxv : ∀ o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)),
      x (Additive.ofMul (⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ : K)) = 0) :
    HFun K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u) h' x y u =
      ∑ o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)),
        h' ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ := by
  classical
  have h1 : h' 1 = 0 := by
    have h := hh' 1 1
    simp only [mul_one, ofMul_one, map_zero, OneMemClass.coe_one, mul_zero, sub_zero, sub_self] at h
    linear_combination -h

  have hval : ∀ (o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))
      (k : ZMod (Function.minimalPeriod (u • ·) o.out)),
      u * Subgroup.transferFunction K u (u⁻¹ • ((u ^ (ZMod.cast k : ℤ)) • o.out)) =
        if k = 0 then u ^ Function.minimalPeriod (u • ·) o.out * o.out.out
        else u ^ (ZMod.cast k : ℤ) * o.out.out := by
    intro o k
    have h := Subgroup.transferTransversal_apply'' u o k
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, Subgroup.transferTransversal_apply, smul_eq_mul] at h
    exact h
  have hsecval : ∀ (o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))
      (k : ZMod (Function.minimalPeriod (u • ·) o.out)),
      Subgroup.transferFunction K u ((u ^ (ZMod.cast k : ℤ)) • o.out) = u ^ (ZMod.cast k : ℤ) * o.out.out := by
    intro o k
    rw [← Subgroup.transferTransversal_apply, Subgroup.transferTransversal_apply']
  rw [HFun]
  rw [← (Subgroup.quotientEquivSigmaZMod K u).symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Fintype.sum_congr _ _ (fun o => ?_)
  rw [Fintype.sum_eq_single (0 : ZMod (Function.minimalPeriod (u • ·) o.out))]
  ·
    have hγ : gam K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u)
        ((Subgroup.quotientEquivSigmaZMod K u).symm ⟨o, 0⟩) u =
        ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ := by
      apply Subtype.ext
      simp only [coe_gam, Subgroup.quotientEquivSigmaZMod_symm_apply]
      rw [mul_assoc, hval o 0, if_pos rfl, hsecval o 0]
      simp only [ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
    rw [hγ, hxv o, zero_mul, add_zero]
  · intro k hk
    have hγ : gam K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u)
        ((Subgroup.quotientEquivSigmaZMod K u).symm ⟨o, k⟩) u = 1 := by
      apply Subtype.ext
      simp only [coe_gam, Subgroup.quotientEquivSigmaZMod_symm_apply, OneMemClass.coe_one]
      rw [mul_assoc, hval o k, if_neg hk, hsecval o k, inv_mul_cancel]
    rw [hγ, h1, ofMul_one, map_zero, zero_mul, add_zero]

theorem coresFun_subtype (χ : Additive G →+ R) (g : G) :
    coresFun K sec hsec (χ.comp (MonoidHom.toAdditive K.subtype)) g =
      (Fintype.card (G ⧸ K) : R) * χ (Additive.ofMul g) := by
  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹
  have hsum : ∑ q : G ⧸ K, χ (Additive.ofMul (sec (g⁻¹ • q))) = ∑ q : G ⧸ K, χ (Additive.ofMul (sec q)) :=
    hb.sum_comp (fun q => χ (Additive.ofMul (sec q)))
  have hpt : ∀ q : G ⧸ K, (χ.comp (MonoidHom.toAdditive K.subtype)) (Additive.ofMul (gam K sec hsec q g)) =
      - χ (Additive.ofMul (sec q)) + χ (Additive.ofMul g) + χ (Additive.ofMul (sec (g⁻¹ • q))) := by
    intro q
    show χ (Additive.ofMul ((gam K sec hsec q g : K) : G)) = _
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [coresFun, Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end CoresPrimitive
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

section Rows

open MulAction

def IsPar (Φ : Subgroup SL(2, ℤ)) {A : Type*} [AddCommGroup A] (φ : Additive Φ →+ A) : Prop :=
  ∀ γ : Φ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

variable {R : Type*} [CommRing R]

def parSub (Φ : Subgroup SL(2, ℤ)) (R : Type*) [CommRing R] : Submodule R (Additive Φ →+ R) where
  carrier := {φ | IsPar Φ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

theorem monoidHom_SL2Z_eq_one [Invertible (6 : R)] (f : SL(2, ℤ) →* Multiplicative R) : f = 1 := by
  have hS4 : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by decide
  have hST6 : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by decide
  have hinv6 : ⅟(6 : R) * 6 = 1 := invOf_mul_self _
  set a : R := Multiplicative.toAdd (f ModularGroup.S) with ha_def
  set b : R := Multiplicative.toAdd (f ModularGroup.T) with hb_def
  have h1 : (4 : R) * a = 0 := by
    have h := congrArg (fun x : SL(2, ℤ) => Multiplicative.toAdd (f x)) hS4
    simp only [map_pow, toAdd_pow, map_one, toAdd_one] at h
    simpa [nsmul_eq_mul] using h
  have h2 : (6 : R) * a + 6 * b = 0 := by
    have h := congrArg (fun x : SL(2, ℤ) => Multiplicative.toAdd (f x)) hST6
    simp only [map_pow, map_mul, toAdd_pow, toAdd_mul, map_one, toAdd_one] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_add] at h
    linear_combination h
  have ha : a = 0 := by
    linear_combination (9 * ⅟(6 : R) ^ 2) * h1 + (-6 * ⅟(6 : R) * a - a) * hinv6
  have hb : b = 0 := by
    rw [ha, mul_zero, zero_add] at h2
    linear_combination ⅟(6 : R) * h2 + (-b) * hinv6
  have hfS : f ModularGroup.S = 1 := by
    rw [← ofAdd_toAdd (f ModularGroup.S), ← ha_def, ha, ofAdd_zero]
  have hfT : f ModularGroup.T = 1 := by
    rw [← ofAdd_toAdd (f ModularGroup.T), ← hb_def, hb, ofAdd_zero]
  refine MonoidHom.ext (fun g => ?_)
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  rw [MonoidHom.one_apply]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hfS
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hfT
  | one => exact map_one f
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
  | inv x _ hx => rw [map_inv, hx, inv_one]

theorem cuspSum_character_eq_zero (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (χ : Additive Φ →+ R) : cuspSum Φ (fun g => χ (Additive.ofMul g)) = 0 := by
  classical
  have key := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
    (AddMonoidHom.toMultiplicativeRight χ) ModularGroup.T
  have htriv : MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight χ) =
      (1 : SL(2, ℤ) →* Multiplicative R) := monoidHom_SL2Z_eq_one _
  rw [htriv, MonoidHom.one_apply] at key
  have key2 := congrArg Multiplicative.toAdd key
  rw [toAdd_one, toAdd_prod] at key2
  rw [cuspSum]
  refine Eq.trans ?_ key2.symm
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [cuspGen]

theorem cuspSum_eq_zero_of_map_mul (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (d : Φ → R) (hd : ∀ g g', d (g * g') = d g + d g') : cuspSum Φ d = 0 := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    rw [one_mul] at h
    linear_combination -h
  let χ : Additive Φ →+ R :=
    { toFun := fun x => d (Additive.toMul x)
      map_zero' := hd1
      map_add' := fun x y => hd (Additive.toMul x) (Additive.toMul y) }
  exact cuspSum_character_eq_zero Φ χ

theorem cuspSum_sub (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (f g : Φ → R) :
    cuspSum Φ (f - g) = cuspSum Φ f - cuspSum Φ g := by
  simp [cuspSum, Finset.sum_sub_distrib]

theorem cuspSum_primitive_congr (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (f f' : Φ → R) (c : Φ → Φ → R) (hf : ∀ g g', f (g * g') = f g + f g' - c g g')
    (hf' : ∀ g g', f' (g * g') = f' g + f' g' - c g g') : cuspSum Φ f = cuspSum Φ f' := by
  have h := cuspSum_eq_zero_of_map_mul Φ (f - f') (by
    intro g g'
    simp only [Pi.sub_apply, hf, hf']
    ring)
  rwa [cuspSum_sub, sub_eq_zero] at h

theorem pairF_instIndep (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (inst₁ inst₂ : IsFreeGroup Φ) [Invertible (2 : R)] [Invertible (6 : R)] (φ ψ : Additive Φ →+ R) :
    @pairF Φ _ R _ inst₁ _ φ ψ = @pairF Φ _ R _ inst₂ _ φ ψ := by
  unfold pairF
  rw [cuspSum_primitive_congr Φ (@hPrim Φ _ R _ inst₁ φ ψ) (@hPrim Φ _ R _ inst₂ φ ψ) (omega φ ψ)
    (@hPrim_mul Φ _ R _ inst₁ φ ψ) (@hPrim_mul Φ _ R _ inst₂ φ ψ)]

theorem omega_self {Φ : Type*} [Group Φ] (φ : Additive Φ →+ R) (g g' : Φ) : omega φ φ g g' = 0 := by
  simp only [omega]
  ring

theorem pairF_add_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ₁ φ₂ ψ : Additive Φ →+ R) :
    pairF Φ (φ₁ + φ₂) ψ = pairF Φ φ₁ ψ + pairF Φ φ₂ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim (φ₁ + φ₂) ψ) (hPrim φ₁ ψ + hPrim φ₂ ψ)
    (omega (φ₁ + φ₂) ψ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.add_apply, hPrim_mul, omega_add_left]
      ring)
  rw [pairF, pairF, pairF, h, cuspSum_add]
  ring

theorem pairF_smul_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (r : R) (φ ψ : Additive Φ →+ R) :
    pairF Φ (r • φ) ψ = r * pairF Φ φ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim (r • φ) ψ) (r • hPrim φ ψ)
    (omega (r • φ) ψ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.smul_apply, smul_eq_mul, hPrim_mul, omega_smul_left]
      ring)
  rw [pairF, pairF, h, cuspSum_smul]
  ring

theorem pairF_swap (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ ψ : Additive Φ →+ R) : pairF Φ ψ φ = - pairF Φ φ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim ψ φ) (-hPrim φ ψ)
    (omega ψ φ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.neg_apply, hPrim_mul, omega_swap φ ψ]
      ring)
  have hneg : cuspSum Φ (-hPrim φ ψ) = - cuspSum Φ (hPrim φ ψ) := by
    simp [cuspSum, Finset.sum_neg_distrib]
  rw [pairF, pairF, h, hneg]
  ring

theorem pairF_self (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ : Additive Φ →+ R) : pairF Φ φ φ = 0 := by
  have h := cuspSum_eq_zero_of_map_mul Φ (hPrim φ φ) (by
    intro g g'
    rw [hPrim_mul, omega_self, sub_zero])
  rw [pairF, h, mul_zero]

noncomputable def cores {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex]
    (x : Additive Φ' →+ R) : Additive Φ →+ R :=
  MonoidHom.toAdditiveLeft
    (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom))))

def res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (y : Additive Φ →+ R) : Additive Φ' →+ R :=
  y.comp (MonoidHom.toAdditive (Subgroup.inclusion h))

def IsParabolicElt {Φ : Subgroup SL(2, ℤ)} (v : Φ) : Prop :=
  ((v : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4

theorem cusp_tower (Φ' Φ : Subgroup SL(2, ℤ)) (hle : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex] :
    ∃ e : Cusp Φ' ≃ Σ q : Cusp Φ,
        Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ Φ'.subgroupOf Φ)),
      ∀ (q : Cusp Φ) (o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ Φ'.subgroupOf Φ))),
        ∃ c' : Φ',
          ((cuspGen Φ' (e.symm ⟨q, o⟩) : Φ') : SL(2, ℤ)) =
            (c' : SL(2, ℤ)) *
              (((o.out.out : Φ) : SL(2, ℤ))⁻¹ *
                ((cuspGen Φ q : Φ) : SL(2, ℤ)) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out *
                ((o.out.out : Φ) : SL(2, ℤ))) *
              (c' : SL(2, ℤ))⁻¹ := by
  exact ModularCurve.PDPairing.CuspTower.cusp_tower_abstract ModularGroup.T hle

theorem inv_conj_pow {G : Type*} [Group G] (a b : G) (i : ℕ) : (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := by
  have h := @conj_pow G _ i a⁻¹ b
  simpa using h

theorem trace_conj_T_pow (a : SL(2, ℤ)) (n : ℕ) :
    ((a⁻¹ * ModularGroup.T ^ n * a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ← zpow_natCast]
  have h := ModularGroup.coe_T_zpow (n : ℤ)
  rw [show ((ModularGroup.T ^ (n : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (ModularGroup.T ^ (n : ℤ)).1
    from rfl, h, Matrix.trace_fin_two_of]
  ring

theorem trace_conj_pow_cuspGen (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp Φ) (c : SL(2, ℤ)) (m : ℕ) :
    ((c⁻¹ * ((cuspGen Φ q : Φ) : SL(2, ℤ)) ^ m * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  have hu : ((cuspGen Φ q : Φ) : SL(2, ℤ)) =
      q.out.out⁻¹ * ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out) * q.out.out := rfl
  rw [hu, inv_conj_pow, ← pow_mul]
  have e : c⁻¹ * (q.out.out⁻¹ * ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out * m) *
      q.out.out) * c = (q.out.out * c)⁻¹ *
        ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out * m) * (q.out.out * c) := by
    group
  rw [e]
  exact trace_conj_T_pow _ _

theorem isParabolicElt_cuspGen (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp Φ) :
    IsParabolicElt (cuspGen Φ q) := by
  have h := trace_conj_pow_cuspGen Φ q 1 1
  simp only [inv_one, pow_one, one_mul, mul_one] at h
  unfold IsParabolicElt
  rw [h]
  norm_num

theorem pairF_cores_left {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex]
    [IsFreeGroup Φ] [IsFreeGroup Φ'] [Invertible (2 : R)]
    [Invertible (6 : R)] (x : Additive Φ' →+ R) (y : Additive Φ →+ R)
    (hx : IsPar Φ' x) (hy : IsPar Φ y) :
    pairF Φ (cores h x) y = pairF Φ' x (res h y) := by
  classical

  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Φ ⧸ K) := Fintype.ofFinite _
  haveI hFq : ∀ u : Φ, Fintype (Quotient (orbitRel (Subgroup.zpowers u) (Φ ⧸ K))) :=
    fun u => Fintype.ofFinite _
  let e : K ≃* Φ' := Subgroup.subgroupOfEquivOfLe h
  let f : Φ' → R := hPrim x (res h y)
  let h' : K → R := fun k => f (e k)
  let xK : Additive K →+ R := x.comp (MonoidHom.toAdditive e.toMonoidHom)

  have hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (xK (Additive.ofMul k) * y (Additive.ofMul ((k' : Φ))) - y (Additive.ofMul (k : Φ)) * xK (Additive.ofMul k')) := by
    intro k k'
    show f (e (k * k')) = f (e k) + f (e k') - _
    rw [map_mul]
    show hPrim x (res h y) (e k * e k') = _
    rw [hPrim_mul]
    rfl

  have hf_conj : ∀ (c v : Φ'), IsParabolicElt v → f (c * v * c⁻¹) = f v := by
    intro c v hv
    exact hPrim_conj_of_apply_eq_zero x (res h y) v (hx v hv) (hy (Subgroup.inclusion h v) hv) c

  have hcor : ∀ g : Φ, coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q) xK g =
      (cores h x) (Additive.ofMul g) := by
    intro g
    rw [coresFun_eq]
    rfl
  have stepA : cuspSum Φ (hPrim (cores h x) y) =
      cuspSum Φ (HFun K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y) := by
    refine cuspSum_primitive_congr Φ _ _ (omega (cores h x) y) (hPrim_mul _ _) ?_
    intro g g'
    rw [HFun_mul K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y hh' g g', hcor, hcor]
    rfl

  have stepB : ∀ q : Cusp Φ,
      HFun K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y (cuspGen Φ q) =
        ∑ o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ K)),
          h' ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ := by
    intro q
    have hyu : y (Additive.ofMul (cuspGen Φ q)) = 0 := hy _ (isParabolicElt_cuspGen Φ q)
    have hsc := HFun_secChange K (Subgroup.transferFunction K (cuspGen Φ q))
      (Subgroup.coe_transferFunction (cuspGen Φ q)) Quotient.out (fun q => QuotientGroup.out_eq' q)
      h' xK y hh' (cuspGen Φ q)
    rw [hyu, mul_zero, zero_mul, add_zero] at hsc
    rw [hsc]
    refine HFun_transferFunction_eq K (cuspGen Φ q) h' xK y hh' ?_
    intro o

    show x (Additive.ofMul (e ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out *
      o.out.out, QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩)) = 0
    apply hx
    show (( (o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out : Φ) :
      SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_pow_cuspGen]
    norm_num

  obtain ⟨E, hE⟩ := cusp_tower Φ' Φ h
  have stepC : cuspSum Φ' f =
      ∑ q : Cusp Φ, ∑ o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ K)),
        h' ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ := by
    rw [cuspSum, ← E.symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun o _ => ?_))
    obtain ⟨c', hc'⟩ := hE q o

    have hv : cuspGen Φ' (E.symm ⟨q, o⟩) =
        c' * e ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    rw [hv, hf_conj]
    ·
      show (( (o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out : Φ) :
        SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_pow_cuspGen]
      norm_num

  rw [pairF, pairF, stepA, cuspSum, Finset.sum_congr rfl (fun q _ => stepB q), ← stepC]

section PlusMinus
open Matrix Matrix.SpecialLinearGroup ModularGroup

theorem conj_entries (b u : SL(2, ℤ)) (i j : Fin 2) :
    (b * u * b⁻¹) i j = ∑ l, ∑ k, b i k * u k l * (adjugate (b : Matrix (Fin 2) (Fin 2) ℤ)) l j := by
  rw [coe_mul, coe_mul, coe_inv, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]

theorem unipotent_normal_form (u : SL(2, ℤ)) (htr : (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hu : u ≠ 1) :
    ∃ (b : SL(2, ℤ)) (m : ℤ), m ≠ 0 ∧ u = b⁻¹ * T ^ m * b := by

  have hdet : (u : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := u.2
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet

  have hN : (u 0 0 - 1) * (u 1 1 - 1) - u 0 1 * u 1 0 = 0 := by linear_combination hdet - htr
  have hαδ : (u 0 0 - 1) + (u 1 1 - 1) = 0 := by linear_combination htr

  have hex : ∃ v0 v1 : ℤ, (v0 ≠ 0 ∨ v1 ≠ 0) ∧ (u 0 0 - 1) * v0 + u 0 1 * v1 = 0 ∧
      u 1 0 * v0 + (u 1 1 - 1) * v1 = 0 := by
    by_cases hc : u 0 0 - 1 = 0 ∧ u 1 0 = 0
    ·
      refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩
      · rw [hc.1]; ring
      · rw [hc.2]; ring
    ·
      refine ⟨u 0 0 - 1, u 1 0, ?_, ?_, ?_⟩
      · by_contra hcon
        push Not at hcon
        exact hc hcon
      · linear_combination (u 0 0 - 1) * hαδ - hN
      · linear_combination (u 1 0) * hαδ
  obtain ⟨v0, v1, hv, hk0, hk1⟩ := hex

  have hg : 0 < Int.gcd v0 v1 := Int.gcd_pos_iff.mpr hv
  obtain ⟨w0, w1, hw, hv0, hv1⟩ := Int.exists_gcd_one hg
  set d : ℤ := (Int.gcd v0 v1 : ℤ) with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact_mod_cast hg.ne'
  have hk0' : (u 0 0 - 1) * w0 + u 0 1 * w1 = 0 := by
    have : d * ((u 0 0 - 1) * w0 + u 0 1 * w1) = 0 := by
      rw [hv0, hv1] at hk0; linear_combination hk0
    exact (mul_eq_zero.mp this).resolve_left hd0
  have hk1' : u 1 0 * w0 + (u 1 1 - 1) * w1 = 0 := by
    have : d * (u 1 0 * w0 + (u 1 1 - 1) * w1) = 0 := by
      rw [hv0, hv1] at hk1; linear_combination hk1
    exact (mul_eq_zero.mp this).resolve_left hd0

  have hcop : IsCoprime w0 w1 := Int.isCoprime_iff_gcd_eq_one.mpr hw
  obtain ⟨a', b', hab⟩ := hcop

  let bM : Matrix (Fin 2) (Fin 2) ℤ := !![a', b'; -w1, w0]
  have hbdet : bM.det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hab
  let b : SL(2, ℤ) := ⟨bM, hbdet⟩

  set w : SL(2, ℤ) := b * u * b⁻¹ with hwdef
  have hb00 : b 0 0 = a' := rfl
  have hb01 : b 0 1 = b' := rfl
  have hb10 : b 1 0 = -w1 := rfl
  have hb11 : b 1 1 = w0 := rfl
  have hadj : adjugate (b : Matrix (Fin 2) (Fin 2) ℤ) = !![w0, -b'; w1, a'] := by
    rw [show (b : Matrix (Fin 2) (Fin 2) ℤ) = !![a', b'; -w1, w0] from rfl, Matrix.adjugate_fin_two_of]
    simp
  have hw00 : w 0 0 = 1 := by
    rw [hwdef, conj_entries]
    simp only [Fin.sum_univ_two, hadj, hb00, hb01, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination a' * hk0' + b' * hk1' + hab
  have hw10 : w 1 0 = 0 := by
    rw [hwdef, conj_entries]
    simp only [Fin.sum_univ_two, hadj, hb10, hb11, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (-w1) * hk0' + w0 * hk1'
  have hwdet : (w : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := w.2
  rw [Matrix.det_fin_two] at hwdet
  have hw11 : w 1 1 = 1 := by
    have : w 0 0 * w 1 1 - w 0 1 * w 1 0 = 1 := hwdet
    rw [hw00, hw10] at this
    linear_combination this

  have hwT : w = T ^ (w 0 1) := by
    apply Subtype.ext
    rw [show ((T ^ (w 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (w 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hw00
    · rfl
    · exact hw10
    · exact hw11
  refine ⟨b, w 0 1, ?_, ?_⟩
  · intro hm
    apply hu
    have : w = 1 := by rw [hwT, hm, zpow_zero]

    have hu' : u = b⁻¹ * w * b := by rw [hwdef]; group
    rw [hu', this, mul_one, inv_mul_cancel]
  · rw [← hwT, hwdef]
    group

theorem centralizer_T_zpow (m : ℤ) (hm : m ≠ 0) (g : SL(2, ℤ)) (hg : g * T ^ m = T ^ m * g) :
    ∃ j : ℤ, g = T ^ j ∨ g = -T ^ j := by

  have e := fun i j => congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) i j) hg
  have hTm : ((T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] := coe_T_zpow m
  simp only [coe_mul, hTm] at e
  have e00 := e 0 0
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10 e11

  have hg10 : g 1 0 = 0 := by
    have : m * g 1 0 = 0 := by linear_combination -e00
    exact (mul_eq_zero.mp this).resolve_left hm

  have e01 := e 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e01
  have hdiag : g 0 0 = g 1 1 := by
    have : m * (g 0 0 - g 1 1) = 0 := by linear_combination e01
    linear_combination (mul_eq_zero.mp this).resolve_left hm
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.2
  rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero, ← hdiag] at hdet

  have hsq : g 0 0 * g 0 0 = 1 := hdet
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · refine ⟨g 0 1, Or.inl ?_⟩
    have h11 : g 1 1 = 1 := by rw [← hdiag]; exact h1
    apply Subtype.ext
    rw [show ((T ^ (g 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (g 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hg10
    · simpa using h11
  · refine ⟨-(g 0 1), Or.inr ?_⟩
    have h11 : g 1 1 = -1 := by rw [← hdiag]; exact h1
    apply Subtype.ext
    rw [coe_neg, show ((T ^ (-(g 0 1)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (-(g 0 1))).1 from rfl,
      coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hg10
    · simpa using h11

theorem T_zpow_intertwine (m m' : ℤ) (hm : m ≠ 0) (g : SL(2, ℤ)) (hg : g * T ^ m = T ^ m' * g) :
    m = m' ∧ ∃ j : ℤ, g = T ^ j ∨ g = -T ^ j := by
  have e := fun i j => congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) i j) hg
  have hTm : ((T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] := coe_T_zpow m
  have hTm' : ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m'; 0, 1] := coe_T_zpow m'
  simp only [coe_mul, hTm, hTm'] at e
  have e00 := e 0 0
  have e01 := e 0 1
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11

  have hg10 : g 1 0 = 0 := by
    have : m * g 1 0 = 0 := by linear_combination e11
    exact (mul_eq_zero.mp this).resolve_left hm
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.2
  rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero] at hdet

  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hmm : m = m' := by
      have : g 0 0 * m = m' * g 1 1 := by linear_combination e01
      rw [h0, h1] at this; linear_combination this
    refine ⟨hmm, g 0 1, Or.inl ?_⟩
    apply Subtype.ext
    rw [show ((T ^ (g 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (g 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h0
    · simp
    · simpa using hg10
    · simpa using h1
  · have hmm : m = m' := by
      have : g 0 0 * m = m' * g 1 1 := by linear_combination e01
      rw [h0, h1] at this; linear_combination -this
    refine ⟨hmm, -(g 0 1), Or.inr ?_⟩
    apply Subtype.ext
    rw [coe_neg, show ((T ^ (-(g 0 1)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (-(g 0 1))).1 from rfl,
      coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h0
    · simp
    · simpa using hg10
    · simpa using h1

private def _root_.ModularCurve.PDPairing.TD.pm (Φ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Φ ∨ -g ∈ Φ}
  one_mem' := Or.inl Φ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Φ.mul_mem ha hb)
    · right
      have h := Φ.mul_mem ha hb
      rwa [mul_neg] at h
    · right
      have h := Φ.mul_mem ha hb
      rwa [neg_mul] at h
    · left
      have h := Φ.mul_mem ha hb
      rwa [neg_mul, mul_neg, neg_neg] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Φ.inv_mem ha)
    · right
      have h := Φ.inv_mem ha
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      rwa [hinv] at h

p2m_export "ModularCurve.PDPairing.TD" "pm"
theorem le_pm (Φ : Subgroup SL(2, ℤ)) : Φ ≤ pm Φ := fun _ hg => Or.inl hg

theorem mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : g ∈ pm Φ ↔ g ∈ Φ ∨ -g ∈ Φ := Iff.rfl

theorem sanPM_pm_eq (Φ : Subgroup SL(2, ℤ)) : ModularCurve.PDPairing.SanPM.pm Φ = pm Φ := rfl

scoped instance pm_finiteIndex (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] : (pm Φ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pm Φ)

def cuspOf (Δ : Subgroup SL(2, ℤ)) (b : SL(2, ℤ)) : Cusp Δ :=
  Quotient.mk (MulAction.orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Δ)) (b : SL(2, ℤ) ⧸ Δ)

theorem cuspOf_T_zpow_mul (Δ : Subgroup SL(2, ℤ)) (j : ℤ) (b : SL(2, ℤ)) : cuspOf Δ (T ^ j * b) = cuspOf Δ b := by
  apply Quotient.sound
  show ((T ^ j * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) ∈ MulAction.orbit (Subgroup.zpowers T) ((b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ)
  rw [MulAction.mem_orbit_iff]
  exact ⟨⟨T ^ j, Subgroup.zpow_mem_zpowers T j⟩, rfl⟩

theorem cuspOf_mul_mem (Δ : Subgroup SL(2, ℤ)) (b δ : SL(2, ℤ)) (hδ : δ ∈ Δ) : cuspOf Δ (b * δ) = cuspOf Δ b := by
  unfold cuspOf
  rw [QuotientGroup.mk_mul_of_mem b hδ]

theorem cuspOf_neg (Δ : Subgroup SL(2, ℤ)) (hΔ : (-1 : SL(2, ℤ)) ∈ Δ) (b : SL(2, ℤ)) : cuspOf Δ (-b) = cuspOf Δ b := by
  rw [← mul_neg_one]
  exact cuspOf_mul_mem Δ b (-1) hΔ

theorem cuspOf_out (Δ : Subgroup SL(2, ℤ)) (q : Cusp Δ) : cuspOf Δ q.out.out = q := by
  unfold cuspOf
  rw [QuotientGroup.out_eq', Quotient.out_eq]

theorem minimalPeriod_T_zpow_smul (Δ : Subgroup SL(2, ℤ)) (i : ℤ) (x : SL(2, ℤ) ⧸ Δ) :
    Function.minimalPeriod (T • ·) (T ^ i • x) = Function.minimalPeriod (T • ·) x := by
  have key : ∀ n : ℕ, (T ^ n • (T ^ i • x) = T ^ i • x) ↔ (T ^ n • x = x) := by
    intro n
    rw [smul_smul, show T ^ n * T ^ i = T ^ i * T ^ n from by
      rw [← zpow_natCast]; exact zpow_mul_comm T (n : ℤ) i, ← smul_smul]
    exact (MulAction.injective (T ^ i)).eq_iff
  apply Nat.dvd_antisymm
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, key, MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← key, MulAction.pow_smul_eq_iff_minimalPeriod_dvd]

theorem cuspOf_out_out (Δ : Subgroup SL(2, ℤ)) (b : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Δ ∧ ∃ i : ℤ, (cuspOf Δ b).out.out = T ^ i * b * δ ∧
      Function.minimalPeriod (T • ·) (cuspOf Δ b).out =
        Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) := by
  have h1 : (cuspOf Δ b).out ∈ MulAction.orbit (Subgroup.zpowers T) (b : SL(2, ℤ) ⧸ Δ) := by
    rw [← MulAction.orbitRel_apply]
    exact Quotient.exact ((Quotient.out_eq (cuspOf Δ b)).trans rfl)
  rw [MulAction.mem_orbit_iff] at h1
  obtain ⟨⟨t, ht⟩, hx⟩ := h1
  rw [Subgroup.mem_zpowers_iff] at ht
  obtain ⟨i, rfl⟩ := ht
  have hx' : (cuspOf Δ b).out = ((T ^ i * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) := by
    rw [← hx]; rfl
  have h2 : ((T ^ i * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) = ((cuspOf Δ b).out.out : SL(2, ℤ) ⧸ Δ) := by
    rw [QuotientGroup.out_eq', hx']
  have h3 := QuotientGroup.eq.mp h2
  refine ⟨(T ^ i * b)⁻¹ * (cuspOf Δ b).out.out, h3, i, ?_, ?_⟩
  · group
  · rw [hx']
    show Function.minimalPeriod (T • ·) (T ^ i • (b : SL(2, ℤ) ⧸ Δ)) = _
    exact minimalPeriod_T_zpow_smul Δ i _

theorem cuspGen_cuspOf (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex] (b : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Δ ∧ ((cuspGen Δ (cuspOf Δ b) : Δ) : SL(2, ℤ)) =
      δ⁻¹ * (b⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * b) * δ := by
  obtain ⟨δ, hδ, i, hc, hm⟩ := cuspOf_out_out Δ b
  refine ⟨δ, hδ, ?_⟩
  show (cuspOf Δ b).out.out⁻¹ * T ^ Function.minimalPeriod (T • ·) (cuspOf Δ b).out * (cuspOf Δ b).out.out = _
  rw [hm, hc]
  have hcomm : T ^ (-i) * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * T ^ i =
      T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) := by
    rw [← zpow_natCast, ← zpow_add, ← zpow_add]
    congr 1
    ring
  calc (T ^ i * b * δ)⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * (T ^ i * b * δ)
      = δ⁻¹ * (b⁻¹ * (T ^ (-i) * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * T ^ i) * b) * δ := by
        group
    _ = δ⁻¹ * (b⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * b) * δ := by rw [hcomm]

noncomputable def pmRep (Φ : Subgroup SL(2, ℤ)) (g : pm Φ) : Φ := by
  classical
  exact if h : (g : SL(2, ℤ)) ∈ Φ then ⟨g, h⟩ else ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩

theorem trace_intertwine (a V V'' : Matrix (Fin 2) (Fin 2) ℤ) (ha : a.det ≠ 0) (h : a * V = V'' * a) :
    V''.trace = V.trace := by
  have e := fun i j => congrFun (congrFun h i) j
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at ha
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  have key : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * ((V'' 0 0 + V'' 1 1) - (V 0 0 + V 1 1)) = 0 := by
    linear_combination (-(a 1 1)) * h00 + (a 1 0) * h01 + (a 0 1) * h10 + (-(a 0 0)) * h11
  have := (mul_eq_zero.mp key).resolve_left ha
  linear_combination this

theorem pmRep_parabolic {Φ : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] (q : Cusp (pm Φ)) :
    IsParabolicElt (pmRep Φ (cuspGen (pm Φ) q)) := by
  classical
  have h2 : (((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 :=
    isParabolicElt_cuspGen (pm Φ) q
  unfold IsParabolicElt pmRep
  split_ifs with h
  · exact h2
  · show ((-((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [coe_neg, Matrix.trace_neg, neg_sq]
    exact h2

theorem cancel_det {a M M' : Matrix (Fin 2) (Fin 2) ℤ} (ha : a.det ≠ 0) (h : a * M = a * M') : M = M' := by
  have h0 : a * (M - M') = 0 := by rw [Matrix.mul_sub, h, sub_self]
  have h2 : a.det • (M - M') = 0 := by
    calc a.det • (M - M') = (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) * (M - M') := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = adjugate a * a * (M - M') := by rw [Matrix.adjugate_mul]
      _ = adjugate a * (a * (M - M')) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [h0, Matrix.mul_zero]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left ha)

theorem cancel_det_right {a M M' : Matrix (Fin 2) (Fin 2) ℤ} (ha : a.det ≠ 0) (h : M * a = M' * a) : M = M' := by
  have h0 : (M - M') * a = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h2 : a.det • (M - M') = 0 := by
    calc a.det • (M - M') = (M - M') * (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = (M - M') * (a * adjugate a) := by rw [Matrix.mul_adjugate]
      _ = (M - M') * a * adjugate a := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [h0, Matrix.zero_mul]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left ha)

theorem intertwine_pow (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) (n : ℕ) :
    a * ((u ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, coe_mul, coe_mul, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem intertwine_inv (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) :
    a * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  have hu : (u : Matrix (Fin 2) (Fin 2) ℤ) * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hw : ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc a * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) * a *
          ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hw, Matrix.one_mul]
    _ = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (a * (u : Matrix (Fin 2) (Fin 2) ℤ)) *
          ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h, Matrix.mul_assoc _ _ a]
    _ = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]

theorem intertwine_zpow (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) (k : ℤ) :
    a * ((u ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  rcases k with (n | n)
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]; exact intertwine_pow a u w h n
  · rw [zpow_negSucc, zpow_negSucc]; exact intertwine_inv a _ _ (intertwine_pow a u w h (n + 1))

theorem T_zpow_ne_neg_T_zpow (i j : ℤ) : (T ^ i : SL(2, ℤ)) ≠ -T ^ j := by
  intro h
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp only [coe_neg, Matrix.neg_apply] at this
  rw [show ((T ^ i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ i).1 from rfl,
    show ((T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ j).1 from rfl, coe_T_zpow, coe_T_zpow] at this
  simp at this

theorem T_zpow_injective (i j : ℤ) (h : (T ^ i : SL(2, ℤ)) = T ^ j) : i = j := by
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
  rw [show ((T ^ i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ i).1 from rfl,
    show ((T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ j).1 from rfl, coe_T_zpow, coe_T_zpow] at this
  simpa using this

theorem neg_mem_pm {Φ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} (hg : g ∈ pm Φ) : -g ∈ pm Φ := by
  rcases hg with h | h
  · right; rwa [neg_neg]
  · left; exact h

theorem neg_one_mem_pm (Φ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pm Φ := Or.inr (by rw [neg_neg]; exact Φ.one_mem)

theorem pmRep_spec (Φ : Subgroup SL(2, ℤ)) (g : pm Φ) :
    ((pmRep Φ g : Φ) : SL(2, ℤ)) = g ∨ ((pmRep Φ g : Φ) : SL(2, ℤ)) = -(g : SL(2, ℤ)) := by
  classical
  unfold pmRep
  split_ifs with h
  · left; rfl
  · right; rfl

theorem pmRep_unique {Φ : Subgroup SL(2, ℤ)} (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (g : pm Φ) (x : Φ)
    (hx : (x : SL(2, ℤ)) = g ∨ (x : SL(2, ℤ)) = -(g : SL(2, ℤ))) : x = pmRep Φ g := by

  have key : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)
  apply key
  rcases hx with h1 | h1 <;> rcases pmRep_spec Φ g with h2 | h2
  · left; rw [h1, h2]
  · right; rw [h1, h2, neg_neg]
  · right; rw [h1, h2]
  · left; rw [h1, h2]

theorem pmRep_conj {Φ : Subgroup SL(2, ℤ)} (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (δ x : pm Φ) :
    pmRep Φ (δ⁻¹ * x * δ) = (pmRep Φ δ)⁻¹ * pmRep Φ x * pmRep Φ δ := by
  symm
  apply pmRep_unique hΦ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rcases pmRep_spec Φ δ with hd | hd <;> rcases pmRep_spec Φ x with hx | hx <;> rw [hd, hx]
  · left; rfl
  · right; simp [mul_neg, neg_mul]
  · left
    have hinv : (-(δ : SL(2, ℤ)))⁻¹ = -(δ : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [hinv]; simp [mul_neg, neg_mul]
  · right
    have hinv : (-(δ : SL(2, ℤ)))⁻¹ = -(δ : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [hinv]; simp [mul_neg, neg_mul]

noncomputable def pmLift {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (g : pm Φ) : SL(2, ℤ) := by
  classical
  exact if h : (g : SL(2, ℤ)) ∈ Φ then ((e ⟨g, h⟩ : Φ'') : SL(2, ℤ))
    else -((e ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩ : Φ'') : SL(2, ℤ))

theorem pmLift_mem {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (g : pm Φ) : pmLift e g ∈ pm Φ'' := by
  classical
  unfold pmLift
  split_ifs with h
  · exact Or.inl (e ⟨g, h⟩).2
  · right; rw [neg_neg]; exact (e _).2

theorem pmLift_intertwine {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) (g : pm Φ) :
    a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((pmLift e g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  classical
  unfold pmLift
  split_ifs with h
  · exact he ⟨g, h⟩
  · have h1 := he ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩
    simp only [coe_neg, Matrix.mul_neg] at h1
    rw [coe_neg, Matrix.neg_mul, ← h1, neg_neg]

theorem pmRep_pmLift {Φ Φ'' : Subgroup SL(2, ℤ)} (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'') (g : pm Φ) :
    pmRep Φ'' ⟨pmLift e g, pmLift_mem e g⟩ = e (pmRep Φ g) := by
  classical
  symm
  apply pmRep_unique hΦ''
  show ((e (pmRep Φ g) : Φ'') : SL(2, ℤ)) = pmLift e g ∨ ((e (pmRep Φ g) : Φ'') : SL(2, ℤ)) = -pmLift e g
  unfold pmRep pmLift
  split_ifs with h
  · left; rfl
  · right; rw [neg_neg]

theorem minimalPeriod_T_pos (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex] (x : SL(2, ℤ) ⧸ Δ) :
    0 < Function.minimalPeriod (T • ·) x := by
  exact Function.minimalPeriod_pos_of_mem_periodicPts ((MulAction.injective T).mem_periodicPts x)

theorem centralizer_cuspGen_pm (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp (pm Φ)) (z : SL(2, ℤ))
    (hz : z ∈ pm Φ) (hcomm : z * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * z) :
    ∃ k : ℤ, z = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k ∨ z = -((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k := by
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  have hg : (c * z * c⁻¹) * T ^ (m : ℤ) = T ^ (m : ℤ) * (c * z * c⁻¹) := by
    have hT : T ^ (m : ℤ) = c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹ := by rw [hu, zpow_natCast]; group
    rw [hT]
    calc c * z * c⁻¹ * (c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹)
        = c * (z * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ))) * c⁻¹ := by group
      _ = c * (((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * z) * c⁻¹ := by rw [hcomm]
      _ = c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹ * (c * z * c⁻¹) := by group
  obtain ⟨j, hj⟩ := centralizer_T_zpow (m : ℤ) hmz (c * z * c⁻¹) hg

  have hmem : c⁻¹ * T ^ j * c ∈ pm Φ := by
    rcases hj with h | h
    · have : c⁻¹ * T ^ j * c = z := by rw [← h]; group
      rw [this]; exact hz
    · have : c⁻¹ * T ^ j * c = -z := by
        rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group, h]
        simp [mul_neg, neg_mul]
      rw [this]; exact neg_mem_pm hz
  have hfix : T ^ j • q.out = q.out := by
    have hc : (c : SL(2, ℤ) ⧸ pm Φ) = q.out := QuotientGroup.out_eq' q.out
    rw [← hc, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ j * c)⁻¹ * c = (c⁻¹ * T ^ j * c)⁻¹ := by group
    rw [this]
    exact (pm Φ).inv_mem hmem
  have hdvd : (m : ℤ) ∣ j := (MulAction.zpow_smul_eq_iff_minimalPeriod_dvd).mp hfix
  obtain ⟨k, hk⟩ := hdvd
  have hpow : c⁻¹ * T ^ j * c = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k := by
    rw [hu, hk, zpow_mul, zpow_natCast]
    have := @conj_zpow SL(2, ℤ) _ k c⁻¹ (T ^ m)
    simp only [inv_inv] at this
    exact this.symm
  refine ⟨k, ?_⟩
  rcases hj with h | h
  · left
    rw [← hpow, ← h]; group
  · right
    rw [← hpow]
    have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
    rw [this, h]
    simp [mul_neg, neg_mul]

theorem hat_spec {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (_hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (_hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) (q : Cusp (pm Φ)) :
    ∃ (b : SL(2, ℤ)) (m' : ℤ), 0 < m' ∧ pmLift e (cuspGen (pm Φ) q) = b⁻¹ * T ^ m' * b ∧
      (Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') : ℤ) = m' := by
  set u : pm Φ := cuspGen (pm Φ) q with hudef
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((u : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out
  set w : SL(2, ℤ) := pmLift e u with hwdef
  have hint : a * ((u : pm Φ) : SL(2, ℤ)) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a := pmLift_intertwine e a he u

  have htru : (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    have h := trace_conj_pow_cuspGen (pm Φ) q 1 1
    simpa using h
  have htrw : (w : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [trace_intertwine a _ _ (ne_of_gt ha) hint]; exact htru
  have hTm_ne : (T ^ m : SL(2, ℤ)) ≠ 1 := by
    intro h
    have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    rw [← zpow_natCast, show ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (m : ℤ)).1 from rfl,
      coe_T_zpow] at this
    simp at this
    omega
  have hu_ne : ((u : pm Φ) : SL(2, ℤ)) ≠ 1 := by
    rw [hu]; intro h
    apply hTm_ne
    calc (T ^ m : SL(2, ℤ)) = c * (c⁻¹ * T ^ m * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hw_ne : w ≠ 1 := by
    intro h
    apply hu_ne
    apply Subtype.ext
    have h1 : a * (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = a * ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [hint, h, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
    exact cancel_det (ne_of_gt ha) h1

  obtain ⟨b, m', hm'0, hwb⟩ := unipotent_normal_form w htrw hw_ne

  have hposT : ∀ n : ℤ, IsPosUnipotent ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ↔ 0 < n := by
    intro n
    rw [show ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ n).1 from rfl, coe_T_zpow]
    simp [IsPosUnipotent]

  have hcu : (c : Matrix (Fin 2) (Fin 2) ℤ) * (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * c := by
    rw [← coe_mul, ← coe_mul, hu, zpow_natCast]
    congr 1; group
  have htrT : ∀ n : ℤ, (((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace = 2 := by
    intro n
    rw [show ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ n).1 from rfl, coe_T_zpow,
      Matrix.trace_fin_two_of]; ring
  have hupos : IsPosUnipotent (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    have key := isPosUnipotent_intertwine (c : Matrix (Fin 2) (Fin 2) ℤ)
      (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [c.2]; exact one_pos) hcu.symm htru (u : SL(2, ℤ)).2 (htrT _) (T ^ (m : ℤ)).2
      (fun h => hu_ne (Subtype.ext h))
    rw [key, hposT]
    exact_mod_cast hm
  have hwpos : IsPosUnipotent (w : Matrix (Fin 2) (Fin 2) ℤ) := by
    have key := isPosUnipotent_intertwine a (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (w : Matrix (Fin 2) (Fin 2) ℤ) ha hint.symm htru (u : SL(2, ℤ)).2 htrw w.2 (fun h => hu_ne (Subtype.ext h))
    exact key.mp hupos
  have hm'pos : 0 < m' := by

    have hbw : (b : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) =
        ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * b := by
      rw [← coe_mul, ← coe_mul, hwb]; congr 1; group
    have key := isPosUnipotent_intertwine (b : Matrix (Fin 2) (Fin 2) ℤ)
      (w : Matrix (Fin 2) (Fin 2) ℤ) ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (by rw [b.2]; exact one_pos)
      hbw.symm htrw w.2 (htrT _) (T ^ m').2 (fun h => hw_ne (Subtype.ext h))
    exact (hposT m').mp (key.mp hwpos)
  refine ⟨b, m', hm'pos, hwb, ?_⟩

  set n : ℕ := Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') with hndef
  have hwmem : w ∈ pm Φ'' := pmLift_mem e u

  have h1 : (n : ℤ) ∣ m' := by
    rw [← MulAction.zpow_smul_eq_iff_minimalPeriod_dvd, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ m' * b)⁻¹ * b = (b⁻¹ * T ^ m' * b)⁻¹ := by group
    rw [this, ← hwb]
    exact (pm Φ'').inv_mem hwmem

  have hzmem : b⁻¹ * T ^ n * b ∈ pm Φ'' := by
    have hfix : T ^ n • (b : SL(2, ℤ) ⧸ pm Φ'') = (b : SL(2, ℤ) ⧸ pm Φ'') :=
      (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hfix
    have : (T ^ n * b)⁻¹ * b = (b⁻¹ * T ^ n * b)⁻¹ := by group
    rw [this] at hfix
    exact (Subgroup.inv_mem_iff _).mp hfix
  set z : pm Φ'' := ⟨b⁻¹ * T ^ n * b, hzmem⟩ with hzdef
  set z₀ : Φ'' := pmRep Φ'' z with hz₀def
  set y : Φ := e.symm z₀ with hydef
  have hz₀ : ((z₀ : Φ'') : SL(2, ℤ)) = b⁻¹ * T ^ n * b ∨ ((z₀ : Φ'') : SL(2, ℤ)) = -(b⁻¹ * T ^ n * b) :=
    pmRep_spec Φ'' z

  have hcommz : ((z₀ : Φ'') : SL(2, ℤ)) * w = w * ((z₀ : Φ'') : SL(2, ℤ)) := by
    have base : (b⁻¹ * T ^ n * b) * (b⁻¹ * T ^ m' * b) = (b⁻¹ * T ^ m' * b) * (b⁻¹ * T ^ n * b) := by
      rw [← zpow_natCast]
      calc b⁻¹ * T ^ (n : ℤ) * b * (b⁻¹ * T ^ m' * b) = b⁻¹ * (T ^ (n : ℤ) * T ^ m') * b := by group
        _ = b⁻¹ * (T ^ m' * T ^ (n : ℤ)) * b := by rw [zpow_mul_comm]
        _ = b⁻¹ * T ^ m' * b * (b⁻¹ * T ^ (n : ℤ) * b) := by group
    rw [hwb]
    rcases hz₀ with h | h <;> rw [h]
    · exact base
    · rw [neg_mul, mul_neg, base]

  have hy : a * ((y : Φ) : SL(2, ℤ)) = (((z₀ : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
    have := he y
    rw [hydef, MulEquiv.apply_symm_apply] at this
    rw [hydef]; exact this
  have hcommy : ((y : Φ) : SL(2, ℤ)) * ((u : pm Φ) : SL(2, ℤ)) = ((u : pm Φ) : SL(2, ℤ)) * ((y : Φ) : SL(2, ℤ)) := by
    apply Subtype.ext
    apply cancel_det (ne_of_gt ha)
    rw [coe_mul, coe_mul, ← Matrix.mul_assoc, hy, Matrix.mul_assoc, hint, ← Matrix.mul_assoc, ← coe_mul, hcommz,
      coe_mul, Matrix.mul_assoc, ← hy, ← Matrix.mul_assoc, ← hint, Matrix.mul_assoc]
  obtain ⟨k, hk⟩ := centralizer_cuspGen_pm Φ q ((y : Φ) : SL(2, ℤ)) (le_pm Φ y.2) hcommy

  have hwk : a * (((u : pm Φ) : SL(2, ℤ)) ^ k : SL(2, ℤ)) = ((w ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a :=
    intertwine_zpow a _ _ hint k
  have hz₀wk : ((z₀ : Φ'') : SL(2, ℤ)) = w ^ k ∨ ((z₀ : Φ'') : SL(2, ℤ)) = -w ^ k := by
    rcases hk with h | h
    · left
      apply Subtype.ext
      apply cancel_det_right (ne_of_gt ha)
      rw [← hy, h, hwk]
    · right
      apply Subtype.ext
      apply cancel_det_right (ne_of_gt ha)
      rw [← hy, h, coe_neg, coe_neg, Matrix.mul_neg, hwk, Matrix.neg_mul]

  have hwkb : w ^ k = b⁻¹ * T ^ (m' * k) * b := by
    rw [hwb, zpow_mul]
    have := @conj_zpow SL(2, ℤ) _ k b⁻¹ (T ^ m')
    simp only [inv_inv] at this
    exact this
  have hnk : (n : ℤ) = m' * k := by
    rcases hz₀ with h1' | h1' <;> rcases hz₀wk with h2 | h2
    ·
      apply T_zpow_injective
      rw [zpow_natCast]
      have : b⁻¹ * T ^ n * b = b⁻¹ * T ^ (m' * k) * b := by rw [← h1', h2, hwkb]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (b⁻¹ * T ^ (m' * k) * b) * b⁻¹ := by rw [this]
        _ = T ^ (m' * k) := by group
    · exfalso
      apply T_zpow_ne_neg_T_zpow (n : ℤ) (m' * k)
      rw [zpow_natCast]
      have : b⁻¹ * T ^ n * b = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← h1', h2, hwkb]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (-(b⁻¹ * T ^ (m' * k) * b)) * b⁻¹ := by rw [this]
        _ = -T ^ (m' * k) := by simp [mul_neg, neg_mul]; group
    · exfalso
      apply T_zpow_ne_neg_T_zpow (n : ℤ) (m' * k)
      rw [zpow_natCast]
      have : -(b⁻¹ * T ^ n * b) = b⁻¹ * T ^ (m' * k) * b := by rw [← h1', h2, hwkb]
      have this' : b⁻¹ * T ^ n * b = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← this, neg_neg]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (-(b⁻¹ * T ^ (m' * k) * b)) * b⁻¹ := by rw [this']
        _ = -T ^ (m' * k) := by simp [mul_neg, neg_mul]; group
    · apply T_zpow_injective
      rw [zpow_natCast]
      have : -(b⁻¹ * T ^ n * b) = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← h1', h2, hwkb]
      have this' : b⁻¹ * T ^ n * b = b⁻¹ * T ^ (m' * k) * b := neg_injective this
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (b⁻¹ * T ^ (m' * k) * b) * b⁻¹ := by rw [this']
        _ = T ^ (m' * k) := by group
  have h2 : m' ∣ (n : ℤ) := ⟨k, hnk⟩
  have hnpos : (0 : ℤ) < n := by exact_mod_cast minimalPeriod_T_pos (pm Φ'') (b : SL(2, ℤ) ⧸ pm Φ'')
  exact Int.dvd_antisymm hnpos.le hm'pos.le h1 h2

theorem hat_roundtrip {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a a' : Matrix (Fin 2) (Fin 2) ℤ) (_ha : 0 < a.det) (_ha' : 0 < a'.det)
    (_he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (_he' : ∀ g : Φ'', a' * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a')
    (q : Cusp (pm Φ)) (b : SL(2, ℤ)) (m' : ℤ)
    (hwb : pmLift e (cuspGen (pm Φ) q) = b⁻¹ * T ^ m' * b)
    (hn : (Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') : ℤ) = m')
    (b₂ : SL(2, ℤ)) (m₂ : ℤ) (hm₂ : 0 < m₂)
    (hwb₂ : pmLift e.symm (cuspGen (pm Φ'') (cuspOf (pm Φ'') b)) = b₂⁻¹ * T ^ m₂ * b₂) :
    cuspOf (pm Φ) b₂ = q ∧ ∃ cc : Φ'', pmRep Φ'' (cuspGen (pm Φ'') (cuspOf (pm Φ'') b)) =
      cc * e (pmRep Φ (cuspGen (pm Φ) q)) * cc⁻¹ := by
  set u : pm Φ := cuspGen (pm Φ) q with hudef
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((u : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out

  obtain ⟨δ, hδ, hgen⟩ := cuspGen_cuspOf (pm Φ'') b
  have hgen' : ((cuspGen (pm Φ'') (cuspOf (pm Φ'') b) : pm Φ'') : SL(2, ℤ)) = δ⁻¹ * pmLift e u * δ := by
    rw [hgen, hwb, ← zpow_natCast, hn]
  set u'' : pm Φ'' := cuspGen (pm Φ'') (cuspOf (pm Φ'') b) with hu''def
  have hu''eq : u'' = (⟨δ, hδ⟩ : pm Φ'')⁻¹ * ⟨pmLift e u, pmLift_mem e u⟩ * ⟨δ, hδ⟩ := Subtype.ext hgen'

  have hrep : pmRep Φ'' u'' = (pmRep Φ'' ⟨δ, hδ⟩)⁻¹ * e (pmRep Φ u) * pmRep Φ'' ⟨δ, hδ⟩ := by
    rw [hu''eq, pmRep_conj hΦ'', pmRep_pmLift hΦ'' e u]
  refine ⟨?_, (pmRep Φ'' ⟨δ, hδ⟩)⁻¹, by rw [hrep, inv_inv]⟩

  have hrep₂ : pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ = e.symm (pmRep Φ'' u'') :=
    pmRep_pmLift hΦ e.symm u''
  rw [hrep, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at hrep₂
  set φ : Φ := e.symm (pmRep Φ'' ⟨δ, hδ⟩) with hφdef

  have hX : ((pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ : Φ) : SL(2, ℤ)) =
      (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ ∨
      ((pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ : Φ) : SL(2, ℤ)) =
      -((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ) := by
    rw [hrep₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases pmRep_spec Φ u with h2 | h2 <;> rw [h2]
    · left; rfl
    · right; simp [mul_neg, neg_mul]
  have hw₂cases : pmLift e.symm u'' = (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ ∨
      pmLift e.symm u'' = -((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ) := by
    rcases pmRep_spec Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ with h1 | h1 <;> rcases hX with h3 | h3
    · left; exact h1.symm.trans h3
    · right; exact h1.symm.trans h3
    · right
      have h4 : -pmLift e.symm u'' = _ := h1.symm.trans h3
      rw [← neg_neg (pmLift e.symm u''), h4]
    · left
      have h4 : -pmLift e.symm u'' = _ := h1.symm.trans h3
      exact neg_injective h4
  have htrconj : (((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [hu]
    have : (φ : SL(2, ℤ))⁻¹ * (c⁻¹ * T ^ m * c) * φ = (c * φ)⁻¹ * T ^ m * (c * φ) := by group
    rw [this]; exact trace_conj_T_pow _ _
  have htrb₂ : ((b₂⁻¹ * T ^ m₂ * b₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      show ((T ^ m₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ m₂).1 from rfl, coe_T_zpow,
      Matrix.trace_fin_two_of]
    ring
  have htrw₂ : ((pmLift e.symm u'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [hwb₂]; exact htrb₂
  have hw₂eq : pmLift e.symm u'' = (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ := by
    rcases hw₂cases with h | h
    · exact h
    · exfalso
      have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ).trace) h
      simp only [coe_neg, Matrix.trace_neg] at this
      rw [htrw₂, htrconj] at this
      norm_num at this

  have hrig : (c * φ * b₂⁻¹) * T ^ m₂ = T ^ (m : ℤ) * (c * φ * b₂⁻¹) := by
    have h1 : b₂⁻¹ * T ^ m₂ * b₂ = (c * (φ : SL(2, ℤ)))⁻¹ * T ^ (m : ℤ) * (c * φ) := by
      rw [← hwb₂, hw₂eq, hu, zpow_natCast]; group
    calc c * φ * b₂⁻¹ * T ^ m₂ = c * φ * (b₂⁻¹ * T ^ m₂ * b₂) * b₂⁻¹ := by group
      _ = c * φ * ((c * (φ : SL(2, ℤ)))⁻¹ * T ^ (m : ℤ) * (c * φ)) * b₂⁻¹ := by rw [h1]
      _ = T ^ (m : ℤ) * (c * φ * b₂⁻¹) := by group
  obtain ⟨_, j, hj⟩ := T_zpow_intertwine m₂ (m : ℤ) (ne_of_gt hm₂) (c * φ * b₂⁻¹) hrig

  have hφmem : ((φ : Φ) : SL(2, ℤ)) ∈ pm Φ := le_pm Φ φ.2
  have hq : cuspOf (pm Φ) (c * φ) = q := by
    rw [cuspOf_mul_mem (pm Φ) c φ hφmem]
    exact cuspOf_out (pm Φ) q
  rcases hj with h | h
  · have hb₂ : b₂ = T ^ (-j) * (c * φ) := by
      calc b₂ = (c * φ * b₂⁻¹)⁻¹ * (c * φ) := by group
        _ = (T ^ j)⁻¹ * (c * φ) := by rw [h]
        _ = T ^ (-j) * (c * φ) := by rw [zpow_neg]
    rw [hb₂, cuspOf_T_zpow_mul, hq]
  · have hb₂ : b₂ = -(T ^ (-j) * (c * φ)) := by
      have hinv : (-(T ^ j : SL(2, ℤ)))⁻¹ = -(T ^ j)⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      calc b₂ = (c * φ * b₂⁻¹)⁻¹ * (c * φ) := by group
        _ = (-(T ^ j))⁻¹ * (c * φ) := by rw [h]
        _ = -(T ^ (-j) * (c * φ)) := by rw [hinv, zpow_neg, neg_mul]
    rw [hb₂, cuspOf_neg (pm Φ) (neg_one_mem_pm Φ), cuspOf_T_zpow_mul, hq]

theorem cusp_pm_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) :
    ∃ β : Cusp (pm Φ) ≃ Cusp (pm Φ''), ∀ q : Cusp (pm Φ), ∃ c : Φ'',
      pmRep Φ'' (cuspGen (pm Φ'') (β q)) = c * e (pmRep Φ (cuspGen (pm Φ) q)) * c⁻¹ := by
  classical

  have hane : a.det ≠ 0 := ne_of_gt ha
  have he' : ∀ g : Φ'', adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a := by
    intro g
    have h := he (e.symm g)
    rw [MulEquiv.apply_symm_apply] at h

    have h2 : a.det • ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a) =
        a.det • (adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
      calc a.det • ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a)
          = (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) * ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
              adjugate a) := by rw [Matrix.smul_mul, Matrix.one_mul]
        _ = adjugate a * (a * (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * adjugate a := by
              rw [← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = adjugate a * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) * adjugate a := by rw [h]
        _ = adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (a * adjugate a) := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = a.det • (adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
              rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
    exact ((smul_right_injective (Matrix (Fin 2) (Fin 2) ℤ) hane) h2).symm
  have ha' : 0 < (adjugate a).det := by
    rw [Matrix.det_adjugate]; simpa using ha

  have S := fun q => hat_spec hΦ hΦ'' e a ha he q
  have S' := fun q'' => hat_spec hΦ'' hΦ e.symm (adjugate a) ha' he' q''
  choose bq mq hmq hwq hnq using S
  choose bq' mq' hmq' hwq' hnq' using S'
  have he'' : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm.symm g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
    intro g; rw [MulEquiv.symm_symm]; exact he g
  refine ⟨⟨fun q => cuspOf (pm Φ'') (bq q), fun q'' => cuspOf (pm Φ) (bq' q''), ?_, ?_⟩, ?_⟩
  · intro q
    exact (hat_roundtrip hΦ hΦ'' e a (adjugate a) ha ha' he he' q (bq q) (mq q) (hwq q) (hnq q)
      (bq' (cuspOf (pm Φ'') (bq q))) (mq' _) (hmq' _) (hwq' _)).1
  · intro q''
    have hr := hat_roundtrip hΦ'' hΦ e.symm (adjugate a) a ha' ha he' he'' q'' (bq' q'') (mq' q'') (hwq' q'')
      (hnq' q'') (bq (cuspOf (pm Φ) (bq' q''))) (mq _) (hmq _) (by rw [MulEquiv.symm_symm]; exact hwq _)
    exact hr.1
  · intro q
    exact (hat_roundtrip hΦ hΦ'' e a (adjugate a) ha ha' he he' q (bq q) (mq q) (hwq q) (hnq q)
      (bq' (cuspOf (pm Φ'') (bq q))) (mq' _) (hmq' _) (hwq' _)).2

theorem cuspSum_eq_two_mul_sum_pm (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (hΦ : (-1 : SL(2, ℤ)) ∉ Φ)
    (F : Φ → R) (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → F (v ^ k) = k * F v) :
    cuspSum Φ F = 2 * ∑ q : Cusp (pm Φ), F (pmRep Φ (cuspGen (pm Φ) q)) := by
  classical
  set K : Subgroup (pm Φ) := Φ.subgroupOf (pm Φ) with hK
  haveI : Fintype (pm Φ ⧸ K) := Fintype.ofFinite _
  haveI hFq : ∀ u : pm Φ, Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K))) :=
    fun _ => Fintype.ofFinite _

  have sgn : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)

  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨-1, neg_one_mem_pm Φ⟩, fun b => ?_⟩
    simp only [hK, Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg, mul_one]
    rcases b.2 with hb | hb
    · right
      refine ⟨hb, fun hnb => hΦ ?_⟩
      have : (-(b : SL(2, ℤ))) * (b : SL(2, ℤ))⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel]
      rw [← this]; exact Φ.mul_mem hnb (Φ.inv_mem hb)
    · left
      refine ⟨hb, fun hb' => hΦ ?_⟩
      have : (-(b : SL(2, ℤ))) * (b : SL(2, ℤ))⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel]
      rw [← this]; exact Φ.mul_mem hb (Φ.inv_mem hb')
  have hcard : Fintype.card (pm Φ ⧸ K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact hidx
  obtain ⟨E, hE⟩ := cusp_tower Φ (pm Φ) (le_pm Φ)
  rw [cuspSum, ← E.symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  set u : pm Φ := cuspGen (pm Φ) q with hudef

  have htrk : ∀ (O : SL(2, ℤ)) (k : ℕ),
      ((O⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * O : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    intro O k
    rw [trace_conj_pow_cuspGen (pm Φ) q O k]; norm_num
  have hupow : ∀ k : ℕ, ((u : pm Φ) : SL(2, ℤ)) ^ k = ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k ∨
      ((u : pm Φ) : SL(2, ℤ)) ^ k = -((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k := by
    intro k
    rcases pmRep_spec Φ u with h | h
    · left; rw [h]
    · have hu' : ((u : pm Φ) : SL(2, ℤ)) = -((pmRep Φ u : Φ) : SL(2, ℤ)) := by rw [h, neg_neg]
      rw [hu', neg_pow]
      rcases neg_one_pow_eq_or SL(2, ℤ) k with h1 | h1
      · left; rw [h1, one_mul]
      · right; rw [h1, neg_one_mul]
  have hparpow : ∀ k : ℕ, IsParabolicElt ((pmRep Φ u : Φ) ^ k) := by
    intro k
    unfold IsParabolicElt
    have h4 := htrk 1 k
    simp only [inv_one, one_mul, mul_one] at h4
    rw [Subgroup.coe_pow]
    rcases hupow k with h | h
    · rw [← h]; exact h4
    · have : ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k = -(((u : pm Φ) : SL(2, ℤ)) ^ k) := by rw [h, neg_neg]
      rw [this, coe_neg, Matrix.trace_neg, neg_sq]; exact h4
  have step1 : ∀ o : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K)),
      F (cuspGen Φ (E.symm ⟨q, o⟩)) = (Function.minimalPeriod (u • ·) o.out : R) * F (pmRep Φ u) := by
    intro o
    obtain ⟨c', hc'⟩ := hE q o
    set k : ℕ := Function.minimalPeriod (u • ·) o.out with hkdef
    set O : pm Φ := o.out.out with hOdef
    have hvmem : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) ∈ Φ := by
      have h := QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    set v : Φ := ⟨_, hvmem⟩ with hvdef
    have hgen : cuspGen Φ (E.symm ⟨q, o⟩) = c' * v * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    have hvpar : IsParabolicElt v := htrk O k

    set φ : Φ := pmRep Φ O with hφdef
    have hconj : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) =
        (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * φ := by
      rcases pmRep_spec Φ O with h | h
      · rw [h]
      · have hO : ((O : pm Φ) : SL(2, ℤ)) = -(φ : SL(2, ℤ)) := by rw [h, neg_neg]
        have hinv : (-(φ : SL(2, ℤ)))⁻¹ = -(φ : SL(2, ℤ))⁻¹ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
        rw [hO, hinv, neg_mul, neg_mul, mul_neg, neg_neg]
    have hv : v = φ⁻¹ * (pmRep Φ u) ^ k * φ := by
      apply sgn
      simp only [hvdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hconj]
      rcases hupow k with h | h
      · left; rw [h]
      · right; rw [h]; simp [mul_neg, neg_mul]
    rw [hgen, hF_conj c' v hvpar, hv]
    have h2 := hF_conj φ⁻¹ ((pmRep Φ u) ^ k) (hparpow k)
    rw [inv_inv] at h2
    rw [h2, hF_pow _ k (pmRep_parabolic q)]
  rw [Finset.sum_congr rfl (fun o _ => step1 o), ← Finset.sum_mul]
  congr 1

  have step2' : ∑ o : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K)),
      (Function.minimalPeriod (u • ·) o.out : ℕ) = Fintype.card (pm Φ ⧸ K) := by
    rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers u) (pm Φ ⧸ K)), Fintype.card_sigma]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [MulAction.minimalPeriod_eq_card]
    exact Fintype.card_congr (Equiv.refl _)
  have step2 := step2'.trans hcard
  have := congrArg (fun n : ℕ => (n : R)) step2
  simpa [Nat.cast_sum] using this

end PlusMinus
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

theorem cuspSum_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (f : Φ'' → R) (hf_conj : ∀ (c v : Φ''), IsParabolicElt v → f (c * v * c⁻¹) = f v)
    (hf_pow : ∀ (v : Φ'') (k : ℕ), IsParabolicElt v → f (v ^ k) = k * f v) :
    cuspSum Φ (f ∘ e) = cuspSum Φ'' f := by

  have hpar : ∀ v : Φ, IsParabolicElt v → IsParabolicElt (e v) := by
    intro v hv
    unfold IsParabolicElt at hv ⊢
    rw [trace_intertwine a _ _ (ne_of_gt ha) (he v)]
    exact hv
  have hF_conj : ∀ (c v : Φ), IsParabolicElt v → (f ∘ e) (c * v * c⁻¹) = (f ∘ e) v := by
    intro c v hv
    show f (e (c * v * c⁻¹)) = f (e v)
    rw [map_mul, map_mul, map_inv]
    exact hf_conj (e c) (e v) (hpar v hv)
  have hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → (f ∘ e) (v ^ k) = k * (f ∘ e) v := by
    intro v k hv
    show f (e (v ^ k)) = k * f (e v)
    rw [map_pow]
    exact hf_pow (e v) k (hpar v hv)
  rw [cuspSum_eq_two_mul_sum_pm Φ hΦ (f ∘ e) hF_conj hF_pow, cuspSum_eq_two_mul_sum_pm Φ'' hΦ'' f hf_conj hf_pow]
  congr 1
  obtain ⟨β, hβ⟩ := cusp_pm_transport hΦ hΦ'' e a ha he
  rw [← β.sum_comp]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  obtain ⟨c, hc⟩ := hβ q
  show f (e (pmRep Φ (cuspGen (pm Φ) q))) = f (pmRep Φ'' (cuspGen (pm Φ'') (β q)))
  rw [hc, hf_conj]
  exact hpar _ (pmRep_parabolic q)

theorem omega_comp {Φ Φ'' : Type*} [Group Φ] [Group Φ''] (e : Φ →* Φ'') (φ ψ : Additive Φ'' →+ R)
    (g g' : Φ) :
    omega (φ.comp (MonoidHom.toAdditive e)) (ψ.comp (MonoidHom.toAdditive e)) g g' =
      omega φ ψ (e g) (e g') := rfl

theorem pairF_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex] [IsFreeGroup Φ]
    [IsFreeGroup Φ''] [Invertible (2 : R)] [Invertible (6 : R)]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (φ ψ : Additive Φ'' →+ R) (hφ : IsPar Φ'' φ) (hψ : IsPar Φ'' ψ) :
    pairF Φ (φ.comp (MonoidHom.toAdditive e.toMonoidHom)) (ψ.comp (MonoidHom.toAdditive e.toMonoidHom)) =
      pairF Φ'' φ ψ := by
  have step1 : cuspSum Φ (hPrim (φ.comp (MonoidHom.toAdditive e.toMonoidHom))
      (ψ.comp (MonoidHom.toAdditive e.toMonoidHom))) = cuspSum Φ (hPrim φ ψ ∘ e) := by
    refine cuspSum_primitive_congr Φ _ _
      (omega (φ.comp (MonoidHom.toAdditive e.toMonoidHom)) (ψ.comp (MonoidHom.toAdditive e.toMonoidHom)))
      (hPrim_mul _ _) ?_
    intro g g'
    show hPrim φ ψ (e (g * g')) = hPrim φ ψ (e g) + hPrim φ ψ (e g') - _
    rw [map_mul, hPrim_mul]
    rfl
  have step2 : cuspSum Φ (hPrim φ ψ ∘ e) = cuspSum Φ'' (hPrim φ ψ) := by
    refine cuspSum_transport hΦ hΦ'' e a ha he (hPrim φ ψ) ?_ ?_
    · intro c v hv
      exact hPrim_conj_of_apply_eq_zero φ ψ v (hφ v hv) (hψ v hv) c
    · intro v k _
      exact hPrim_pow φ ψ v k
  rw [pairF, pairF, step1, step2]

theorem isPar_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (y : Additive Φ →+ R) (hy : IsPar Φ y) :
    IsPar Φ' (res h y) := by
  intro γ hγ
  exact hy (Subgroup.inclusion h γ) hγ

theorem cores_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (a : Additive Φ →+ R) :
    cores h (res h a) = ((Φ'.relIndex Φ : ℕ) : R) • a := by
  classical
  haveI : Fintype (Φ ⧸ Φ'.subgroupOf Φ) := Fintype.ofFinite _
  apply AddMonoidHom.ext
  intro g'

  obtain ⟨g, rfl⟩ : ∃ g : Φ, Additive.ofMul g = g' := ⟨Additive.toMul g', rfl⟩
  have key := coresFun_eq (Φ'.subgroupOf Φ) (Quotient.out) (fun q => QuotientGroup.out_eq' q)
    (a.comp (MonoidHom.toAdditive (Φ'.subgroupOf Φ).subtype)) g
  rw [coresFun_subtype] at key
  have hcard : (Fintype.card (Φ ⧸ Φ'.subgroupOf Φ) : R) = ((Φ'.relIndex Φ : ℕ) : R) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  rw [AddMonoidHom.smul_apply, smul_eq_mul, ← hcard, key, cores]
  rfl

theorem pairF_res_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex]
    [IsFreeGroup Φ] [IsFreeGroup Φ'] [Invertible (2 : R)] [Invertible (6 : R)]
    (a b : Additive Φ →+ R) (ha : IsPar Φ a) (hb : IsPar Φ b) :
    pairF Φ' (res h a) (res h b) = ((Φ'.relIndex Φ : ℕ) : R) * pairF Φ a b := by
  rw [← pairF_smul_left, ← cores_res h a]
  exact (pairF_cores_left h (res h a) b (isPar_res h a ha) hb).symm

example (Λ₁ Λ₂ Γ : Subgroup SL(2, ℤ)) [IsFreeGroup Λ₂] : IsFreeGroup ↥(Γ ⊓ Λ₁ ⊓ Λ₂) := inferInstance

theorem pairD_indep (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Λ₁.FiniteIndex] [Λ₂.FiniteIndex] [IsFreeGroup Λ₁]
    [IsFreeGroup Λ₂] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Invertible (2 : R)] [Invertible (6 : R)]
    [Invertible (((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R)] [Invertible (((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R)]
    [Invertible (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) (hφ : IsPar Γ φ) (hψ : IsPar Γ ψ) :
    pairD Λ₁ Γ φ ψ = pairD Λ₂ Γ φ ψ := by

  have h1 : Γ ⊓ Λ₁ ⊓ Λ₂ ≤ Γ ⊓ Λ₁ := inf_le_left
  have h2 : Γ ⊓ Λ₁ ⊓ Λ₂ ≤ Γ ⊓ Λ₂ := le_inf (le_trans inf_le_left inf_le_left) inf_le_right
  haveI : IsFreeGroup ↥(Γ ⊓ Λ₁ ⊓ Λ₂) := inferInstance
  have hpar1 : ∀ χ : Additive Γ →+ R, IsPar Γ χ → IsPar (Γ ⊓ Λ₁) (resInf Λ₁ Γ χ) :=
    fun χ hχ γ hγ => hχ _ hγ
  have hpar2 : ∀ χ : Additive Γ →+ R, IsPar Γ χ → IsPar (Γ ⊓ Λ₂) (resInf Λ₂ Γ χ) :=
    fun χ hχ γ hγ => hχ _ hγ

  have hres : ∀ χ : Additive Γ →+ R, res h1 (resInf Λ₁ Γ χ) = res h2 (resInf Λ₂ Γ χ) := by
    intro χ; rfl
  have e1 := pairF_res_res h1 (resInf Λ₁ Γ φ) (resInf Λ₁ Γ ψ) (hpar1 φ hφ) (hpar1 ψ hψ)
  have e2 := pairF_res_res h2 (resInf Λ₂ Γ φ) (resInf Λ₂ Γ ψ) (hpar2 φ hφ) (hpar2 ψ hψ)
  rw [hres φ, hres ψ] at e1

  have hN1 : ((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₁)) * ((Γ ⊓ Λ₁).relIndex Γ) = (Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ :=
    Subgroup.relIndex_mul_relIndex (Γ ⊓ Λ₁ ⊓ Λ₂) (Γ ⊓ Λ₁) Γ h1 inf_le_left
  have hN2 : ((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₂)) * ((Γ ⊓ Λ₂).relIndex Γ) = (Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ :=
    Subgroup.relIndex_mul_relIndex (Γ ⊓ Λ₁ ⊓ Λ₂) (Γ ⊓ Λ₂) Γ h2 inf_le_left
  unfold pairD
  set m₁ : R := (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₁) : ℕ) : R) with hm₁
  set m₂ : R := (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₂) : ℕ) : R) with hm₂
  have hN1' : m₁ * (((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) = (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) := by
    rw [hm₁, ← Nat.cast_mul, hN1]
  have hN2' : m₂ * (((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) = (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) := by
    rw [hm₂, ← Nat.cast_mul, hN2]
  have hiN : ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) = 1 :=
    invOf_mul_self _
  set P₁ := pairF (Γ ⊓ Λ₁) (resInf Λ₁ Γ φ) (resInf Λ₁ Γ ψ) with hP₁
  set P₂ := pairF (Γ ⊓ Λ₂) (resInf Λ₂ Γ φ) (resInf Λ₂ Γ ψ) with hP₂
  set P := pairF (Γ ⊓ Λ₁ ⊓ Λ₂) (res h2 (resInf Λ₂ Γ φ)) (res h2 (resInf Λ₂ Γ ψ)) with hP

  have k1 : (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁) = P := by
    calc (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁)
        = m₁ * ((((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * ⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R)) * P₁ := by
          rw [← hN1']; ring
      _ = m₁ * P₁ := by rw [mul_invOf_self, mul_one]
      _ = P := e1.symm
  have k2 : (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂) = P := by
    calc (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂)
        = m₂ * ((((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * ⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R)) * P₂ := by
          rw [← hN2']; ring
      _ = m₂ * P₂ := by rw [mul_invOf_self, mul_one]
      _ = P := e2.symm
  calc ⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁
      = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) *
          ((((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁)) := by
        rw [← mul_assoc, hiN, one_mul]
    _ = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P := by rw [k1]
    _ = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) *
          ((((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂)) := by rw [k2]
    _ = ⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂ := by rw [← mul_assoc, hiN, one_mul]

end Rows
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

section CDS3Group

open CongruenceSubgroup MulAction Function

variable {R : Type*} [CommRing R]

noncomputable def orbitTransl {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) :
    Quotient (orbitRel (Subgroup.zpowers u') X) ≃ Quotient (orbitRel (Subgroup.zpowers u) X) :=
  Quotient.congr (MulAction.toPerm g) fun a b => by
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    have hpow : ∀ n : ℤ, u' ^ n = g⁻¹ * u ^ n * g := fun n => by
      rw [hu]
      have := @conj_zpow G _ n g⁻¹ u
      simpa using this
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp s.2
      refine ⟨⟨u ^ n, Subgroup.zpow_mem_zpowers u n⟩, ?_⟩
      show u ^ n • g • b = g • a
      have hs' : u' ^ n • b = a := hn ▸ hs
      rw [← hs', hpow, mul_smul, mul_smul, smul_inv_smul]
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp s.2
      refine ⟨⟨u' ^ n, Subgroup.zpow_mem_zpowers u' n⟩, ?_⟩
      show u' ^ n • b = a
      have hs' : u ^ n • g • b = g • a := hn ▸ hs
      rw [hpow, mul_smul, mul_smul, hs', inv_smul_smul]

theorem orbitTransl_mk {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) (x : X) :
    orbitTransl g u u' hu (Quotient.mk _ x) = Quotient.mk _ (g • x) := rfl

theorem minimalPeriod_transl {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) (x : X) :
    minimalPeriod (u • ·) (g • x) = minimalPeriod (u' • ·) x := by
  have hiter : ∀ n : ℕ, u ^ n • g • x = g • (u' ^ n • x) := fun n => by
    rw [hu, inv_conj_pow, mul_smul, mul_smul, smul_inv_smul]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hiter]; exact congrArg _ ((pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl)
  · have h' := (pow_smul_eq_iff_minimalPeriod_dvd (a := u) (b := g • x)
      (n := minimalPeriod (u • ·) (g • x))).mpr dvd_rfl
    rw [hiter] at h'
    exact smul_left_cancel g h'

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex]

omit [Φ.FiniteIndex] in

theorem conj_pow_minimalPeriod_mem (u p : ↥(Gamma 2)) :
    ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
  have h := (pow_smul_eq_iff_minimalPeriod_dvd (a := u) (b := ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
    (n := minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))).mpr dvd_rfl
  rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at h

  rw [← Subgroup.inv_mem_iff]
  convert h using 1
  push_cast
  group

noncomputable def faceVal (F : Φ → R) (u p : ↥(Gamma 2)) : R :=
  F (pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩)

theorem sq_trace_neg (M : Matrix (Fin 2) (Fin 2) ℤ) : (-M).trace ^ 2 = M.trace ^ 2 := by
  rw [Matrix.trace_neg, neg_sq]

theorem sq_trace_conj_pow_SL (b a : SL(2, ℤ)) (k : ℕ) (ha : ((a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ((b⁻¹ * a ^ k * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  exact sq_trace_pow_eq_four a ha k

omit [Φ.FiniteIndex] in
theorem isParabolicElt_pmRep (x : pm Φ) (hx : (((x : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    IsParabolicElt (pmRep Φ x) := by
  unfold IsParabolicElt
  rcases pmRep_spec Φ x with h | h
  · rw [h]; exact hx
  · rw [h, Matrix.SpecialLinearGroup.coe_neg, sq_trace_neg]; exact hx

variable {Φ}

omit [Φ.FiniteIndex] [CommRing R] in

theorem faceVal_eq_of_same_orbit (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (F : Φ → R)
    (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (u : ↥(Gamma 2)) (hu : (((u : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4)
    (p p' : ↥(Gamma 2))
    (h : ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈ orbit (Subgroup.zpowers u) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
    faceVal Φ F u p' = faceVal Φ F u p := by
  rw [mem_orbit_iff] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.2
  have hs' : u ^ j • ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := hj ▸ hs

  have hk : minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [← hs']
    exact ModularCurve.PDPairing.CuspTower.minimalPeriod_zpow_smul u j _

  have hφ : (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
    rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at hs'
    exact hs'
  set k := minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) with hkdef
  set φ : pm Φ := ⟨_, hφ⟩ with hφdef
  set X : pm Φ := ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩ with hXdef
  have hX' : (⟨_, conj_pow_minimalPeriod_mem Φ u p'⟩ : pm Φ) = φ⁻¹ * X * φ := by
    apply Subtype.ext
    show (((p'⁻¹ * u ^ minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p' : ↥(Gamma 2)) : SL(2, ℤ))) =
      ((((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)))⁻¹ *
        ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) *
        (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ))
    rw [hk]
    push_cast
    rw [← zpow_natCast]
    group
  unfold faceVal
  rw [hX', pmRep_conj hΦ φ X]
  have hpar : IsParabolicElt (pmRep Φ X) := by
    apply isParabolicElt_pmRep
    show ((((p⁻¹ * u ^ k * p : ↥(Gamma 2)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    push_cast
    exact sq_trace_conj_pow_SL _ _ _ hu
  have := hF_conj (pmRep Φ φ)⁻¹ (pmRep Φ X) hpar
  rw [inv_inv] at this
  exact this

variable (Φ)

theorem ustd_mem (i : Fin 3) : ModularCurve.PDPairing.BaseTwo.ustd i ∈ Gamma 2 :=
  (ModularCurve.PDPairing.BaseTwo.mem_Gamma_two_iff _).mpr (ModularCurve.PDPairing.BaseTwo.red2_ustd i)

def U (i : Fin 3) : ↥(Gamma 2) := ⟨ModularCurve.PDPairing.BaseTwo.ustd i, ustd_mem i⟩

theorem sq_trace_U (i : Fin 3) : (((U i : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  fin_cases i
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_zero]; simp [Matrix.trace_fin_two_of]
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_one]; simp [Matrix.trace_fin_two_of]
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_two]; simp [Matrix.trace_fin_two_of]

theorem Gamma_two_cusps_TD :
    ∃ e : Cusp (Gamma 2) ≃ Fin 3, ∀ q : Cusp (Gamma 2), ∃ γ : SL(2, ℤ), γ ∈ Gamma 2 ∧
      ((cuspGen (Gamma 2) q : Gamma 2) : SL(2, ℤ)) = γ⁻¹ * ModularCurve.PDPairing.BaseTwo.ustd (e q) * γ :=
  ModularCurve.PDPairing.BaseTwo.Gamma_two_cusps

abbrev OrbitU (i : Fin 3) : Type := Quotient (orbitRel (Subgroup.zpowers (U i)) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))

theorem cuspSum_eq_two_mul_sum_orbitU (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hle : Φ ≤ Gamma 2) [Invertible (6 : R)]
    (F : Φ → R) (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → F (v ^ k) = k * F v) :
    cuspSum Φ F = 2 * ∑ i : Fin 3, ∑ O : OrbitU Φ i, faceVal Φ F (U i) O.out.out := by
  have hle' : pm Φ ≤ Gamma 2 := by
    intro g hg
    rcases hg with hg | hg
    · exact hle hg
    · have := hle hg
      have h1 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
        rw [Gamma_mem]; decide
      simpa using Subgroup.mul_mem _ h1 this
  rw [cuspSum_eq_two_mul_sum_pm Φ hΦ F hF_conj hF_pow]
  congr 1

  obtain ⟨e₁, he₁⟩ := cusp_tower (pm Φ) (Gamma 2) hle'
  obtain ⟨e₂, he₂⟩ := Gamma_two_cusps_TD
  rw [Fintype.sum_equiv e₁ _ (fun qo => F (pmRep Φ (cuspGen (pm Φ) (e₁.symm qo)))) (fun q => by simp),
    Fintype.sum_sigma]

  have inner : ∀ q₂ : Cusp (Gamma 2),
      ∑ o, F (pmRep Φ (cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩))) = ∑ O : OrbitU Φ (e₂ q₂), faceVal Φ F (U (e₂ q₂)) O.out.out := by
    intro q₂
    obtain ⟨γ, hγ, hgen⟩ := he₂ q₂
    set g : ↥(Gamma 2) := ⟨γ, hγ⟩ with hgdef
    have hu : cuspGen (Gamma 2) q₂ = g⁻¹ * U (e₂ q₂) * g := Subtype.ext (by rw [hgen]; rfl)

    have step1 : ∀ o, F (pmRep Φ (cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩))) = faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out := by
      intro o
      obtain ⟨c', hc'⟩ := he₁ q₂ o

      set X : pm Φ := ⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ with hXdef
      have hk : minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) o.out =
          minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
        rw [QuotientGroup.out_eq']
      have hcg : cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩) = (c'⁻¹)⁻¹ * X * c'⁻¹ := by
        apply Subtype.ext
        rw [hc', inv_inv, hXdef]
        push_cast
        rw [hk]
      rw [hcg, pmRep_conj hΦ c'⁻¹ X]
      have hpar : IsParabolicElt (pmRep Φ X) := by
        apply isParabolicElt_pmRep
        show ((((o.out.out⁻¹ * cuspGen (Gamma 2) q₂ ^ _ * o.out.out : ↥(Gamma 2)) : SL(2, ℤ))) :
          Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
        push_cast
        rw [trace_conj_pow_cuspGen]; norm_num
      have := hF_conj (pmRep Φ c'⁻¹)⁻¹ (pmRep Φ X) hpar
      rw [inv_inv] at this
      rw [this]
      rfl
    simp_rw [step1]

    have hpt : ∀ o, faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out =
        faceVal Φ F (U (e₂ q₂)) ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu) o).out.out := by
      intro o

      have hkper := minimalPeriod_transl g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu
        ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))
      rw [Quotient.smul_coe, smul_eq_mul] at hkper
      have hpw : ∀ k : ℕ, cuspGen (Gamma 2) q₂ ^ k = g⁻¹ * U (e₂ q₂) ^ k * g := fun k => by
        rw [hu, inv_conj_pow]
      have hX : (⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ : pm Φ) =
          ⟨_, conj_pow_minimalPeriod_mem Φ (U (e₂ q₂)) (g * o.out.out)⟩ := by
        apply Subtype.ext
        dsimp only
        rw [hkper, hpw]
        push_cast
        group
      have hval : faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out = faceVal Φ F (U (e₂ q₂)) (g * o.out.out) := by
        unfold faceVal
        rw [hX]
      rw [hval]

      have hτ := orbitTransl_mk (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu o.out
      rw [Quotient.out_eq] at hτ
      have h1 : Quotient.mk (orbitRel (Subgroup.zpowers (U (e₂ q₂))) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
          (g • o.out) =
          Quotient.mk _ ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
            (cuspGen (Gamma 2) q₂) hu o).out) :=
        hτ.symm.trans (Quotient.out_eq _).symm
      have h2 : g • o.out ∈ orbit (Subgroup.zpowers (U (e₂ q₂)))
          ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
            (cuspGen (Gamma 2) q₂) hu o).out) :=
        Quotient.exact h1
      have hcoe : (((g * o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) = g • o.out := by
        rw [← smul_eq_mul, ← Quotient.smul_coe, QuotientGroup.out_eq']
      apply faceVal_eq_of_same_orbit hΦ F hF_conj (U (e₂ q₂)) (sq_trace_U (e₂ q₂))
      rw [hcoe, QuotientGroup.out_eq']
      exact h2

    refine Finset.sum_equiv (orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
      (cuspGen (Gamma 2) q₂) hu) (fun o => ?_) (fun o _ => hpt o)
    simp only [Finset.mem_univ]
  simp_rw [inner]
  exact Fintype.sum_equiv e₂ (fun q₂ => ∑ O : OrbitU Φ (e₂ q₂), faceVal Φ F (U (e₂ q₂)) O.out.out)
    (fun i => ∑ O : OrbitU Φ i, faceVal Φ F (U i) O.out.out) (fun q₂ => rfl)

end CDS3Group
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

section CDS3ParFace

open CongruenceSubgroup MulAction Function ModularGroup

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ))

theorem char_conj (ψ : Additive Φ →+ R) (c v : Φ) :
    ψ (Additive.ofMul (c * v * c⁻¹)) = ψ (Additive.ofMul v) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem char_conj' (ψ : Additive Φ →+ R) (c v : Φ) :
    ψ (Additive.ofMul (c⁻¹ * v * c)) = ψ (Additive.ofMul v) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem char_pow (ψ : Additive Φ →+ R) (v : Φ) (k : ℕ) :
    ψ (Additive.ofMul (v ^ k)) = (k : R) * ψ (Additive.ofMul v) := by
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul]

theorem char_zpow (ψ : Additive Φ →+ R) (v : Φ) (k : ℤ) :
    ψ (Additive.ofMul (v ^ k)) = (k : R) * ψ (Additive.ofMul v) := by
  rw [ofMul_zpow, map_zsmul, zsmul_eq_mul]

theorem inv_conj_zpow {G : Type*} [Group G] (a b : G) (i : ℤ) : (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := by
  have h := @conj_zpow G _ i a⁻¹ b
  simpa using h

theorem conj_conj_zpow {G : Type*} [Group G] (δ b X : G) (j : ℤ) :
    δ * (δ⁻¹ * (b⁻¹ * X * b) * δ) ^ j * δ⁻¹ = b⁻¹ * X ^ j * b := by
  rw [show δ⁻¹ * (b⁻¹ * X * b) * δ = (b * δ)⁻¹ * X * (b * δ) by group, inv_conj_zpow]
  group

variable [Φ.FiniteIndex]

theorem exists_eq_conj_cuspGen_zpow (γ : Φ) (htr : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2)
    (hγ : γ ≠ 1) : ∃ (q : Cusp Φ) (δ : Φ) (j : ℤ), γ = δ * cuspGen Φ q ^ j * δ⁻¹ := by
  have hγ' : (γ : SL(2, ℤ)) ≠ 1 := fun h => hγ (Subtype.ext h)
  obtain ⟨b, m, _hm, hγb⟩ := unipotent_normal_form γ htr hγ'

  have hfix : T ^ m • ((b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Φ) = (b : SL(2, ℤ) ⧸ Φ) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ m * b)⁻¹ * b = (γ : SL(2, ℤ))⁻¹ := by rw [hγb]; group
    rw [this]
    exact Φ.inv_mem γ.2
  obtain ⟨j, hj⟩ := (MulAction.zpow_smul_eq_iff_minimalPeriod_dvd).mp hfix
  obtain ⟨δ, hδ, hcg⟩ := cuspGen_cuspOf Φ b
  refine ⟨cuspOf Φ b, ⟨δ, hδ⟩, j, Subtype.ext ?_⟩
  push_cast
  rw [hcg, hγb, hj, zpow_mul, zpow_natCast, conj_conj_zpow]

theorem char_eq_zero_of_trace_two (ψ : Additive Φ →+ R) (hcusp : ∀ q : Cusp Φ, ψ (Additive.ofMul (cuspGen Φ q)) = 0)
    (γ : Φ) (htr : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) : ψ (Additive.ofMul γ) = 0 := by
  by_cases hγ : γ = 1
  · rw [hγ, ofMul_one, map_zero]
  obtain ⟨q, δ, j, h⟩ := exists_eq_conj_cuspGen_zpow Φ γ htr hγ
  rw [h, char_conj, char_zpow, hcusp, mul_zero]

theorem isPar_of_cuspGen [Invertible (2 : R)] (ψ : Additive Φ →+ R)
    (hcusp : ∀ q : Cusp Φ, ψ (Additive.ofMul (cuspGen Φ q)) = 0) : IsPar Φ ψ := by
  intro γ hγ
  have hsq : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsq with h | h
  · exact char_eq_zero_of_trace_two Φ ψ hcusp γ (by linarith)
  · have hneg : ((-(γ : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]; linarith
    have h2 : (((γ ^ 2 : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      have := trace_pow_eq_two_of_trace_eq_two _ (-(γ : SL(2, ℤ))).2 hneg 2
      rw [Matrix.SpecialLinearGroup.coe_neg, neg_sq] at this
      rw [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
      exact this
    have h0 := char_eq_zero_of_trace_two Φ ψ hcusp (γ ^ 2) h2
    rw [char_pow, Nat.cast_ofNat] at h0
    calc ψ (Additive.ofMul γ) = ⅟(2 : R) * (2 * ψ (Additive.ofMul γ)) := by
          rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = 0 := by rw [h0, mul_zero]

variable {Φ}

theorem cuspGen_eq_conj_pmRep_pow (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (Q : Cusp Φ) :
    ∃ (qbar : Cusp (pm Φ)) (c : Φ) (k : ℕ), cuspGen Φ Q = c * pmRep Φ (cuspGen (pm Φ) qbar) ^ k * c⁻¹ := by

  have sgn : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)
  obtain ⟨E, hE⟩ := cusp_tower Φ (pm Φ) (le_pm Φ)

  have key : ∀ (q : Cusp (pm Φ))
      (o : Quotient (orbitRel (Subgroup.zpowers (cuspGen (pm Φ) q)) (pm Φ ⧸ Φ.subgroupOf (pm Φ)))),
      ∃ (c : Φ) (k : ℕ), cuspGen Φ (E.symm ⟨q, o⟩) = c * pmRep Φ (cuspGen (pm Φ) q) ^ k * c⁻¹ := by
    intro q
    set u : pm Φ := cuspGen (pm Φ) q with hudef
    intro o
    obtain ⟨c', hc'⟩ := hE q o
    set k : ℕ := minimalPeriod (u • ·) o.out with hkdef
    set O : pm Φ := o.out.out with hOdef
    have htrk : ∀ (O' : SL(2, ℤ)) (k' : ℕ),
        ((O'⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k' * O' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
      intro O' k'
      rw [trace_conj_pow_cuspGen (pm Φ) q O' k']; norm_num
    have hupow : ∀ k' : ℕ, ((u : pm Φ) : SL(2, ℤ)) ^ k' = ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k' ∨
        ((u : pm Φ) : SL(2, ℤ)) ^ k' = -((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k' := by
      intro k'
      rcases pmRep_spec Φ u with h | h
      · left; rw [h]
      · have hu' : ((u : pm Φ) : SL(2, ℤ)) = -((pmRep Φ u : Φ) : SL(2, ℤ)) := by rw [h, neg_neg]
        rw [hu', neg_pow]
        rcases neg_one_pow_eq_or SL(2, ℤ) k' with h1 | h1
        · left; rw [h1, one_mul]
        · right; rw [h1, neg_one_mul]
    have hvmem : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) ∈ Φ := by
      have h := QuotientGroup.out_conj_pow_minimalPeriod_mem (Φ.subgroupOf (pm Φ)) u o.out
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    set v : Φ := ⟨_, hvmem⟩ with hvdef
    have hgen : cuspGen Φ (E.symm ⟨q, o⟩) = c' * v * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    set φ : Φ := pmRep Φ O with hφdef
    have hconj : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) =
        (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * φ := by
      rcases pmRep_spec Φ O with h | h
      · rw [h]
      · have hO : ((O : pm Φ) : SL(2, ℤ)) = -(φ : SL(2, ℤ)) := by rw [h, neg_neg]
        have hinv : (-(φ : SL(2, ℤ)))⁻¹ = -(φ : SL(2, ℤ))⁻¹ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
        rw [hO, hinv, neg_mul, neg_mul, mul_neg, neg_neg]
    have hv : v = φ⁻¹ * (pmRep Φ u) ^ k * φ := by
      apply sgn
      simp only [hvdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hconj]
      rcases hupow k with h | h
      · left; rw [h]
      · right; rw [h]; simp [mul_neg, neg_mul]
    refine ⟨c' * φ⁻¹, k, ?_⟩
    rw [hgen, hv, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rfl
  obtain ⟨c, k, h⟩ := key (E Q).1 (E Q).2
  rw [Sigma.eta, E.symm_apply_apply] at h
  exact ⟨(E Q).1, c, k, h⟩

omit [Φ.FiniteIndex] in

theorem pm_le_Gamma_two (hle : Φ ≤ Gamma 2) : pm Φ ≤ Gamma 2 := by
  intro g hg
  rcases hg with hg | hg
  · exact hle hg
  · have := hle hg
    have h1 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
      rw [Gamma_mem]; decide
    simpa using Subgroup.mul_mem _ h1 this

set_option maxHeartbeats 1600000 in
theorem cuspGen_pm_eq_conj_faceElt (hle' : pm Φ ≤ Gamma 2) (qbar : Cusp (pm Φ)) :
    ∃ (i : Fin 3) (p : ↥(Gamma 2)) (δ : pm Φ),
      cuspGen (pm Φ) qbar = δ⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ (U i) p⟩ * δ := by
  obtain ⟨e₁, he₁⟩ := cusp_tower (pm Φ) (Gamma 2) hle'
  obtain ⟨e₂, he₂⟩ := Gamma_two_cusps_TD
  have hc0 := he₁ (e₁ qbar).1 (e₁ qbar).2
  clear he₁
  rw [Sigma.eta, e₁.symm_apply_apply] at hc0
  obtain ⟨c', hc'⟩ := hc0
  set q₂ : Cusp (Gamma 2) := (e₁ qbar).1 with hq₂
  set o := (e₁ qbar).2 with ho
  obtain ⟨γ, hγ, hgen⟩ := he₂ q₂
  set g : ↥(Gamma 2) := ⟨γ, hγ⟩ with hgdef
  have hu : cuspGen (Gamma 2) q₂ = g⁻¹ * U (e₂ q₂) * g := Subtype.ext (by rw [hgen]; rfl)
  have hk : minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) o.out =
      minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [QuotientGroup.out_eq']
  have hcg : cuspGen (pm Φ) qbar = (c'⁻¹)⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ * c'⁻¹ := by
    apply Subtype.ext
    rw [hc', inv_inv]
    push_cast
    rw [hk]
  have hkper := minimalPeriod_transl g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu
    ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))
  rw [Quotient.smul_coe, smul_eq_mul] at hkper
  have hpw : ∀ k : ℕ, cuspGen (Gamma 2) q₂ ^ k = g⁻¹ * U (e₂ q₂) ^ k * g := fun k => by rw [hu, inv_conj_pow]
  have hX : (⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ : pm Φ) =
      ⟨_, conj_pow_minimalPeriod_mem Φ (U (e₂ q₂)) (g * o.out.out)⟩ := by
    apply Subtype.ext
    dsimp only
    rw [hkper, hpw]
    push_cast
    group
  exact ⟨e₂ q₂, g * o.out.out, c'⁻¹, by rw [hcg, hX]⟩

omit [Φ.FiniteIndex] in

theorem faceElt_conj_of_same_orbit (u p p' : ↥(Gamma 2))
    (h : ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers u) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
    ∃ φ : pm Φ, (⟨_, conj_pow_minimalPeriod_mem Φ u p'⟩ : pm Φ) = φ⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩ * φ := by
  rw [mem_orbit_iff] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.2
  have hs' : u ^ j • ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := hj ▸ hs
  have hk : minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [← hs']
    exact ModularCurve.PDPairing.CuspTower.minimalPeriod_zpow_smul u j _
  have hφ : (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
    rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at hs'
    exact hs'
  refine ⟨⟨_, hφ⟩, Subtype.ext ?_⟩
  show (((p'⁻¹ * u ^ minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p' : ↥(Gamma 2)) : SL(2, ℤ))) =
    ((((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)))⁻¹ *
      ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) *
      (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ))
  rw [hk]
  push_cast
  rw [← zpow_natCast]
  group

theorem isPar_of_faceElt [Invertible (2 : R)] (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hle : Φ ≤ Gamma 2)
    (ψ : Additive Φ →+ R) (rep : ∀ i : Fin 3, OrbitU Φ i → ↥(Gamma 2))
    (hrep : ∀ (i : Fin 3) (O : OrbitU Φ i),
      Quotient.mk _ (((rep i O : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = O)
    (hface : ∀ (i : Fin 3) (O : OrbitU Φ i),
      ψ (Additive.ofMul (pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ (U i) (rep i O)⟩)) = 0) :
    IsPar Φ ψ := by
  apply isPar_of_cuspGen
  intro Q
  obtain ⟨qbar, c, k, hQ⟩ := cuspGen_eq_conj_pmRep_pow hΦ Q
  rw [hQ, char_conj, char_pow]
  obtain ⟨i, p, δ, hqbar⟩ := cuspGen_pm_eq_conj_faceElt (pm_le_Gamma_two hle) qbar
  rw [hqbar, pmRep_conj hΦ δ, char_conj']
  have h1 : Quotient.mk (orbitRel (Subgroup.zpowers (U i)) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
      ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      Quotient.mk _ (((rep i (Quotient.mk _ ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
        ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [hrep]
  have hmem : ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers (U i)) (((rep i (Quotient.mk _ ((p : ↥(Gamma 2)) :
        ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) :=
    Quotient.exact h1
  obtain ⟨φ, hφ⟩ := faceElt_conj_of_same_orbit (Φ := Φ) (U i) (rep i _) p hmem
  rw [hφ, pmRep_conj hΦ φ, char_conj', hface, mul_zero]

end CDS3ParFace
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

end ModularCurve.PDPairing.TD
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace Schreier
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] {ι : Type*} (a : ι → G)

theorem wprod_nil : wprod a [] = 1 := by simp [wprod]

theorem wprod_append (l l' : List (ι × Bool)) : wprod a (l ++ l') = wprod a l * wprod a l' := by
  simp [wprod, List.map_append, List.prod_append]

theorem wprod_replicate (p : ι × Bool) (k : ℕ) : wprod a (List.replicate k p) = act a p ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, wprod_nil, pow_zero]
  | succ k ih => rw [List.replicate_succ, wprod_cons, ih, ← pow_succ']

theorem wprod_flatten_replicate (l : List (ι × Bool)) (k : ℕ) :
    wprod a (List.replicate k l).flatten = wprod a l ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, wprod_nil, pow_zero]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, wprod_append, ih, ← pow_succ']

end ModularCurve.PDPairing.Schreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace TD
p2m_open "ModularCurve.PDPairing ModularCurve"

section GlueA

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]

theorem minimalPeriod_semiconj {X Y : Type*} (e : X → Y) (he : Injective e) (f : X → X) (g : Y → Y)
    (h : ∀ x, e (f x) = g (e x)) (x : X) : minimalPeriod g (e x) = minimalPeriod f x := by
  rw [minimalPeriod_eq_minimalPeriod_iff]
  intro n
  have hiter : ∀ m : ℕ, (g^[m]) (e x) = e ((f^[m]) x) := by
    intro m
    induction m generalizing x with
    | zero => rfl
    | succ m ih => rw [iterate_succ_apply, iterate_succ_apply, ← h, ih]
  unfold IsPeriodicPt IsFixedPt
  rw [hiter]
  exact ⟨fun hx => he hx, fun hx => congrArg e hx⟩

variable (Φ : Subgroup SL(2, ℤ))

abbrev VΦ : Type := ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup

noncomputable abbrev sanL : Fin 2 → ↥sanovSubgroup := fun i => sanovBasis i

theorem range_sanL : Set.range sanL = {⟨sanovA, sanovA_mem⟩, ⟨sanovB, sanovB_mem⟩} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl sanovBasis_zero
    · exact Or.inr sanovBasis_one
  · rintro (rfl | rfl)
    · exact ⟨0, sanovBasis_zero⟩
    · exact ⟨1, sanovBasis_one⟩

theorem closure_range_sanL : Subgroup.closure (Set.range sanL) = ⊤ := by
  rw [range_sanL]; exact closure_sanov_generators_eq_top

def v0 : VΦ Φ := ((1 : ↥sanovSubgroup) : VΦ Φ)

theorem sanov_transitive (v : VΦ Φ) : ∃ g : ↥sanovSubgroup, g • v0 Φ = v := by
  induction v using QuotientGroup.induction_on with
  | H g => exact ⟨g, by rw [v0, Quotient.smul_coe, smul_eq_mul, mul_one]⟩

noncomputable def treeT : TreeTransversal sanL (v0 Φ) :=
  bfsTransversal sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ)

theorem stabilizer_v0 : stabilizer (↥sanovSubgroup) (v0 Φ) = Φ.subgroupOf sanovSubgroup :=
  stabilizer_quotient _

noncomputable def stabEquiv (hΦs : Φ ≤ sanovSubgroup) : ↥(stabilizer (↥sanovSubgroup) (v0 Φ)) ≃* Φ :=
  (MulEquiv.subgroupCongr (stabilizer_v0 Φ)).trans (Subgroup.subgroupOfEquivOfLe hΦs)

theorem coe_stabEquiv (hΦs : Φ ≤ sanovSubgroup) (x : stabilizer (↥sanovSubgroup) (v0 Φ)) :
    ((stabEquiv Φ hΦs x : Φ) : SL(2, ℤ)) = (((x : stabilizer (↥sanovSubgroup) (v0 Φ)) : ↥sanovSubgroup) : SL(2, ℤ)) := rfl

def faceRound : Fin 3 → List (Fin 2 × Bool)
  | 0 => [(0, true)]
  | 1 => [(1, false)]
  | 2 => [(0, false), (1, true)]

def faceWord (i : Fin 3) (k : ℕ) : List (Fin 2 × Bool) := (List.replicate k (faceRound i)).flatten

noncomputable def faceGen (i : Fin 3) : ↥sanovSubgroup := wprod sanL (faceRound i)

theorem wprod_faceWord (i : Fin 3) (k : ℕ) : wprod sanL (faceWord i k) = faceGen i ^ k :=
  wprod_flatten_replicate sanL (faceRound i) k

theorem faceGen_zero : faceGen 0 = sanovBasis 0 := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ↓reduceIte]

theorem faceGen_one : faceGen 1 = (sanovBasis 1)⁻¹ := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ↓reduceIte]

theorem faceGen_two : faceGen 2 = (sanovBasis 0)⁻¹ * sanovBasis 1 := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ↓reduceIte]

theorem coe_faceGen_zero : ((faceGen 0 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovA := by
  rw [faceGen_zero, sanovBasis_zero]

theorem coe_faceGen_one : ((faceGen 1 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovB⁻¹ := by
  rw [faceGen_one, Subgroup.coe_inv, sanovBasis_one]

theorem coe_faceGen_two : ((faceGen 2 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovA⁻¹ * sanovB := by
  rw [faceGen_two, Subgroup.coe_mul, Subgroup.coe_inv, sanovBasis_zero, sanovBasis_one]

noncomputable def faceLen (i : Fin 3) (v : VΦ Φ) : ℕ := minimalPeriod ((faceGen i) • ·) v

theorem faceWord_closed (i : Fin 3) (v : VΦ Φ) : wprod sanL (faceWord i (faceLen Φ i v)) • v = v := by
  rw [wprod_faceWord]
  exact (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

noncomputable def faceElt (i : Fin 3) (v : VΦ Φ) : stabilizer (↥sanovSubgroup) (v0 Φ) :=
  (treeT Φ).wordWalk v (faceWord i (faceLen Φ i v))

theorem coe_faceElt (i : Fin 3) (v : VΦ Φ) :
    ((faceElt Φ i v : stabilizer (↥sanovSubgroup) (v0 Φ)) : ↥sanovSubgroup) =
      ((treeT Φ).t v)⁻¹ * faceGen i ^ faceLen Φ i v * (treeT Φ).t v := by
  rw [faceElt, TreeTransversal.coe_wordWalk_of_closed _ _ _ (faceWord_closed Φ i v), wprod_faceWord]

noncomputable def gOf : Fin 3 → ↥sanovSubgroup
  | 0 => 1
  | 1 => 1
  | 2 => sanovBasis 0

noncomputable def pOf (i : Fin 3) (v : VΦ Φ) : ↥(Gamma 2) :=
  Subgroup.inclusion sanovSubgroup_le_Gamma_two (gOf i * (treeT Φ).t v)

theorem mk_t (v : VΦ Φ) : (((treeT Φ).t v : ↥sanovSubgroup) : VΦ Φ) = v := by
  have h : (treeT Φ).t v • (((1 : ↥sanovSubgroup)) : VΦ Φ) = v := (treeT Φ).t_smul v
  rw [Quotient.smul_coe, smul_eq_mul, mul_one] at h
  exact h

def β2 : VΦ Φ → ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) := sanToG2 Φ

theorem β2_mk (g : ↥sanovSubgroup) :
    β2 Φ (g : VΦ Φ) = ((Subgroup.inclusion sanovSubgroup_le_Gamma_two g : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) :=
  rfl

theorem β2_smul (g : ↥sanovSubgroup) (x : VΦ Φ) :
    β2 Φ (g • x) = (Subgroup.inclusion sanovSubgroup_le_Gamma_two g) • β2 Φ x :=
  sanToG2_smul Φ g x

theorem β2_injective (hΦs : Φ ≤ sanovSubgroup) : Injective (β2 Φ) := sanToG2_injective Φ hΦs

theorem β2_surjective : Surjective (β2 Φ) := sanToG2_surjective Φ

noncomputable def β2Equiv (hΦs : Φ ≤ sanovSubgroup) : VΦ Φ ≃ ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Equiv.ofBijective (β2 Φ) ⟨β2_injective Φ hΦs, β2_surjective Φ⟩

theorem mk_pOf (i : Fin 3) (v : VΦ Φ) :
    ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = β2 Φ (gOf i • v) := by
  conv_rhs => rw [← mk_t Φ v, Quotient.smul_coe, smul_eq_mul, β2_mk]
  rfl

theorem coe_U_zero : ((U 0 : ↥(Gamma 2)) : SL(2, ℤ)) = sanovA := by
  apply Subtype.ext
  show ((ModularCurve.PDPairing.BaseTwo.ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_zero, coe_sanovA]

theorem coe_U_one : ((U 1 : ↥(Gamma 2)) : SL(2, ℤ)) = sanovB⁻¹ := by
  show ModularCurve.PDPairing.BaseTwo.ustd 1 = sanovB⁻¹
  decide

theorem coe_U_two : ((U 2 : ↥(Gamma 2)) : SL(2, ℤ)) = -(sanovA * (sanovA⁻¹ * sanovB) * sanovA⁻¹) := by
  show ModularCurve.PDPairing.BaseTwo.ustd 2 = -(sanovA * (sanovA⁻¹ * sanovB) * sanovA⁻¹)
  decide

def negOneG2 : ↥(Gamma 2) := ⟨-1, by rw [Gamma_mem]; decide⟩

theorem negOneG2_smul (x : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) : negOneG2 • x = x := by
  induction x using QuotientGroup.induction_on with
  | H q =>
    have hmem : negOneG2 ∈ (pm Φ).subgroupOf (Gamma 2) := by
      rw [Subgroup.mem_subgroupOf]; exact neg_one_mem_pm Φ
    have hcomm : negOneG2 * q = q * negOneG2 :=
      Subtype.ext (by show (-1 : SL(2, ℤ)) * q = q * (-1 : SL(2, ℤ)); rw [neg_one_mul, mul_neg_one])
    rw [Quotient.smul_coe, smul_eq_mul, hcomm, QuotientGroup.mk_mul_of_mem q hmem]

theorem coe_pOf_zero (v : VΦ Φ) : ((pOf Φ 0 v : ↥(Gamma 2)) : SL(2, ℤ)) = (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 0 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 0 = 1 from rfl, one_mul]

theorem coe_pOf_one (v : VΦ Φ) : ((pOf Φ 1 v : ↥(Gamma 2)) : SL(2, ℤ)) = (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 1 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 1 = 1 from rfl, one_mul]

theorem coe_pOf_two (v : VΦ Φ) :
    ((pOf Φ 2 v : ↥(Gamma 2)) : SL(2, ℤ)) = sanovA * (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 2 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 2 = sanovBasis 0 from rfl, Subgroup.coe_mul, sanovBasis_zero]

theorem U_smul_β2 (i : Fin 3) (y : VΦ Φ) :
    U i • β2 Φ (gOf i • y) = β2 Φ (gOf i • (faceGen i • y)) := by
  fin_cases i
  ·
    have hU : U 0 = Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 0) :=
      Subtype.ext (by rw [coe_U_zero, sanovBasis_zero]; rfl)
    show U 0 • β2 Φ ((1 : ↥sanovSubgroup) • y) = β2 Φ ((1 : ↥sanovSubgroup) • (faceGen 0 • y))
    rw [one_smul, one_smul, faceGen_zero, hU, β2_smul]
  · have hU : U 1 = Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 1)⁻¹ :=
      Subtype.ext (by rw [coe_U_one, map_inv, Subgroup.coe_inv, sanovBasis_one]; rfl)
    show U 1 • β2 Φ ((1 : ↥sanovSubgroup) • y) = β2 Φ ((1 : ↥sanovSubgroup) • (faceGen 1 • y))
    rw [one_smul, one_smul, faceGen_one, hU, β2_smul]
  ·
    have hU : U 2 = negOneG2 * Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 0 * faceGen 2 * (sanovBasis 0)⁻¹) := by
      apply Subtype.ext
      rw [coe_U_two]
      show _ = (-1 : SL(2, ℤ)) * ((sanovBasis 0 * faceGen 2 * (sanovBasis 0)⁻¹ : ↥sanovSubgroup) : SL(2, ℤ))
      push_cast
      rw [coe_faceGen_two, sanovBasis_zero, neg_one_mul]
    show U 2 • β2 Φ (sanovBasis 0 • y) = β2 Φ (sanovBasis 0 • (faceGen 2 • y))
    rw [hU, mul_smul, negOneG2_smul, ← β2_smul, smul_smul, smul_smul, mul_assoc (sanovBasis 0 * faceGen 2),
      inv_mul_cancel, mul_one]

theorem minimalPeriod_pOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (v : VΦ Φ) :
    minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = faceLen Φ i v := by
  rw [mk_pOf]
  have hinj : Injective (fun y : VΦ Φ => β2 Φ (gOf i • y)) :=
    fun y₁ y₂ h => smul_left_cancel (gOf i) (β2_injective Φ hΦs h)
  exact minimalPeriod_semiconj (fun y : VΦ Φ => β2 Φ (gOf i • y)) hinj ((faceGen i) • ·) ((U i) • ·)
    (fun y => (U_smul_β2 Φ i y).symm) v

theorem pmRep_faceElt (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (v : VΦ Φ) :
    pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ (U i) (pOf Φ i v)⟩ = stabEquiv Φ hΦs (faceElt Φ i v) := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  symm
  apply pmRep_unique hΦ

  show ((stabEquiv Φ hΦs (faceElt Φ i v) : Φ) : SL(2, ℤ)) =
      (((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
        pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ)) ∨
    ((stabEquiv Φ hΦs (faceElt Φ i v) : Φ) : SL(2, ℤ)) =
      -(((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
        pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ))
  rw [coe_stabEquiv, coe_faceElt, minimalPeriod_pOf Φ hΦs]
  fin_cases i
  · left
    push_cast
    rw [coe_faceGen_zero, coe_U_zero, coe_pOf_zero]
  · left
    push_cast
    rw [coe_faceGen_one, coe_U_one, coe_pOf_one]
  ·
    rcases neg_one_pow_eq_or SL(2, ℤ) (faceLen Φ 2 v) with h1 | h1
    · left
      push_cast
      rw [coe_faceGen_two, coe_U_two, coe_pOf_two, neg_pow, h1, one_mul, conj_pow, mul_inv_rev]
      generalize (sanovA⁻¹ * sanovB) ^ faceLen Φ 2 v = X
      group
    · right
      push_cast
      rw [coe_faceGen_two, coe_U_two, coe_pOf_two, neg_pow, h1, neg_one_mul, conj_pow, mul_neg, neg_mul, neg_neg,
        mul_inv_rev]
      generalize (sanovA⁻¹ * sanovB) ^ faceLen Φ 2 v = X
      group

noncomputable def vOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) : VΦ Φ :=
  (gOf i)⁻¹ • (β2Equiv Φ hΦs).symm O.out

theorem mk_pOf_vOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) :
    Quotient.mk _ (((pOf Φ i (vOf Φ hΦs i O) : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = O := by
  rw [mk_pOf, vOf, smul_inv_smul]
  have h : β2 Φ ((β2Equiv Φ hΦs).symm O.out) = O.out := (β2Equiv Φ hΦs).apply_symm_apply O.out
  rw [h]
  exact Quotient.out_eq O

theorem par_faceElt (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (hpar : IsPar Φ ψ) (i : Fin 3) (v : VΦ Φ) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = 0 := by
  rw [← pmRep_faceElt Φ hΦs]
  apply hpar
  apply isParabolicElt_pmRep
  show ((((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
    pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  push_cast
  exact sq_trace_conj_pow_SL _ _ _ (sq_trace_U i)

variable [Φ.FiniteIndex]

theorem isPar_of_faces [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R)
    (hψ : ∀ (i : Fin 3) (v : VΦ Φ), ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = 0) : IsPar Φ ψ := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  have hle : Φ ≤ Gamma 2 := hΦs.trans sanovSubgroup_le_Gamma_two
  refine isPar_of_faceElt hΦ hle ψ (fun i O => pOf Φ i (vOf Φ hΦs i O)) (fun i O => mk_pOf_vOf Φ hΦs i O) ?_
  intro i O
  rw [pmRep_faceElt Φ hΦs]
  exact hψ i _

end GlueA
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section GlueB

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ))

noncomputable def edgeVal (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (i : Fin 2) : R :=
  ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i)))

theorem edgeVal_tree (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (i : Fin 2)
    (h : (treeT Φ).tree v i = true) : edgeVal Φ hΦs ψ v i = 0 := by
  rw [edgeVal, (treeT Φ).x_eq_one_of_tree v i h, map_one, ofMul_one, map_zero]

theorem edgeVal_add (hΦs : Φ ≤ sanovSubgroup) (ψ ψ' : Additive Φ →+ R) :
    edgeVal Φ hΦs (ψ + ψ') = edgeVal Φ hΦs ψ + edgeVal Φ hΦs ψ' := by
  funext v i; rfl

theorem edgeVal_smul (hΦs : Φ ≤ sanovSubgroup) (r : R) (ψ : Additive Φ →+ R) :
    edgeVal Φ hΦs (r • ψ) = r • edgeVal Φ hΦs ψ := by
  funext v i; rfl

def treeKer : Submodule R (VΦ Φ → Fin 2 → R) where
  carrier := {c | ∀ v i, (treeT Φ).tree v i = true → c v i = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro c c' hc hc' v i h
    show c v i + c' v i = 0
    rw [hc v i h, hc' v i h, add_zero]
  smul_mem' := by
    intro r c hc v i h
    show r • c v i = 0
    rw [hc v i h, smul_zero]

theorem eq_zero_of_edgeVal (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (h : edgeVal Φ hΦs ψ = 0) : ψ = 0 := by

  have hgen : ∀ s : stabilizer (↥sanovSubgroup) (v0 Φ), ψ (Additive.ofMul (stabEquiv Φ hΦs s)) = 0 := by
    intro s
    have hs : s ∈ (treeT Φ).schreierClosure := by
      rw [(treeT Φ).schreierClosure_eq_top closure_range_sanL]; exact Subgroup.mem_top s
    induction hs using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨v, i⟩, rfl⟩ := hy
      have := congrFun (congrFun h v) i
      exact this
    | one => rw [map_one, ofMul_one, map_zero]
    | mul y z _ _ ihy ihz => rw [map_mul, ofMul_mul, map_add, ihy, ihz, add_zero]
    | inv y _ ihy => rw [map_inv, ofMul_inv, map_neg, ihy, neg_zero]
  ext g
  have := hgen ((stabEquiv Φ hΦs).symm (Additive.toMul g))
  rw [MulEquiv.apply_symm_apply] at this
  exact this

noncomputable def charOfEdge (hΦs : Φ ≤ sanovSubgroup) (c : VΦ Φ → Fin 2 → R) : Additive Φ →+ R :=
  (TreeTransversal.character sanovBasis c).comp (MonoidHom.toAdditive (stabEquiv Φ hΦs).symm.toMonoidHom)

theorem edgeVal_charOfEdge (hΦs : Φ ≤ sanovSubgroup) (c : VΦ Φ → Fin 2 → R)
    (hc : ∀ v i, (treeT Φ).tree v i = true → c v i = 0) : edgeVal Φ hΦs (charOfEdge Φ hΦs c) = c := by
  funext v i
  show TreeTransversal.character sanovBasis c
      (Additive.ofMul ((stabEquiv Φ hΦs).symm (stabEquiv Φ hΦs ((treeT Φ).x v i)))) = c v i
  rw [MulEquiv.symm_apply_apply]
  exact TreeTransversal.character_x sanovBasis (treeT Φ) c hc v i

theorem edgeVal_injective (hΦs : Φ ≤ sanovSubgroup) : Injective (edgeVal (R := R) Φ hΦs) := by
  intro ψ ψ' h
  have h0 : edgeVal Φ hΦs (ψ - ψ') = 0 := by
    funext v i
    show ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i))) - ψ' (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i))) = 0
    rw [sub_eq_zero]
    exact congrFun (congrFun h v) i
  exact sub_eq_zero.mp (eq_zero_of_edgeVal Φ hΦs _ h0)

noncomputable def edgeCoordFun (hΦs : Φ ≤ sanovSubgroup) : (Additive Φ →+ R) →ₗ[R] treeKer (R := R) Φ where
  toFun ψ := ⟨edgeVal Φ hΦs ψ, fun v i h => edgeVal_tree Φ hΦs ψ v i h⟩
  map_add' ψ ψ' := Subtype.ext (edgeVal_add Φ hΦs ψ ψ')
  map_smul' r ψ := Subtype.ext (edgeVal_smul Φ hΦs r ψ)

theorem edgeCoordFun_bijective (hΦs : Φ ≤ sanovSubgroup) : Bijective (edgeCoordFun (R := R) Φ hΦs) := by
  constructor
  · intro ψ ψ' h
    exact edgeVal_injective Φ hΦs (congrArg Subtype.val h)
  · intro c
    refine ⟨charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R), Subtype.ext ?_⟩
    exact edgeVal_charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R) (fun v i h => c.2 v i h)

noncomputable def edgeCoord (hΦs : Φ ≤ sanovSubgroup) : (Additive Φ →+ R) ≃ₗ[R] treeKer (R := R) Φ :=
  LinearEquiv.ofBijective (edgeCoordFun Φ hΦs) (edgeCoordFun_bijective Φ hΦs)

theorem edgeCoord_apply (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) :
    ((edgeCoord Φ hΦs ψ : treeKer (R := R) Φ) : VΦ Φ → Fin 2 → R) = edgeVal Φ hΦs ψ := rfl

noncomputable def sval (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) (p : Fin 2 × Bool) : R :=
  if p.2 then c w p.1 else -c ((sanL p.1)⁻¹ • w) p.1

noncomputable def walkSum (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : List (Fin 2 × Bool) → R
  | [] => 0
  | p :: l => sval Φ c (wprod sanL l • v) p + walkSum c v l

theorem walkSum_add (c c' : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    walkSum Φ (c + c') v l = walkSum Φ c v l + walkSum Φ c' v l := by
  induction l with
  | nil => simp [walkSum]
  | cons p l ih =>
    simp only [walkSum, ih]
    obtain ⟨i, d⟩ := p
    cases d <;> simp [sval] <;> ring

theorem walkSum_smul (r : R) (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    walkSum Φ (r • c) v l = r * walkSum Φ c v l := by
  induction l with
  | nil => simp [walkSum]
  | cons p l ih =>
    simp only [walkSum, ih]
    obtain ⟨i, d⟩ := p
    cases d <;> simp [sval] <;> ring

theorem char_wordWalk_eq_walkSum (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).wordWalk v l))) = walkSum Φ (edgeVal Φ hΦs ψ) v l := by
  induction l with
  | nil =>
    show ψ (Additive.ofMul (stabEquiv Φ hΦs 1)) = 0
    rw [map_one, ofMul_one, map_zero]
  | cons p l ih =>
    rw [TreeTransversal.wordWalk_cons, map_mul, ofMul_mul, map_add, ih]
    show _ + _ = sval Φ (edgeVal Φ hΦs ψ) (wprod sanL l • v) p + walkSum Φ (edgeVal Φ hΦs ψ) v l
    congr 1
    obtain ⟨i, d⟩ := p
    cases d
    · rw [TreeTransversal.sx_false, map_inv, ofMul_inv, map_neg]
      simp only [sval, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [TreeTransversal.sx_true]
      simp only [sval, ↓reduceIte]
      rfl

theorem char_faceElt_eq_walkSum (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (i : Fin 3) (v : VΦ Φ) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = walkSum Φ (edgeVal Φ hΦs ψ) v (faceWord i (faceLen Φ i v)) :=
  char_wordWalk_eq_walkSum Φ hΦs ψ v _

variable [Φ.FiniteIndex]

theorem isPar_iff_walkSum [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) :
    IsPar Φ ψ ↔ ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ (edgeVal Φ hΦs ψ) v (faceWord i (faceLen Φ i v)) = 0 := by
  constructor
  · intro h i v
    rw [← char_faceElt_eq_walkSum]
    exact par_faceElt Φ hΦs ψ h i v
  · intro h
    apply isPar_of_faces Φ hΦs ψ
    intro i v
    rw [char_faceElt_eq_walkSum]
    exact h i v

def parKer : Submodule R (VΦ Φ → Fin 2 → R) where
  carrier := {c | (∀ v i, (treeT Φ).tree v i = true → c v i = 0) ∧
    ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ c v (faceWord i (faceLen Φ i v)) = 0}
  zero_mem' := ⟨fun _ _ _ => rfl, fun i v => by
    have := walkSum_smul Φ (0 : R) (0 : VΦ Φ → Fin 2 → R) v (faceWord i (faceLen Φ i v))
    rwa [zero_smul, zero_mul] at this⟩
  add_mem' := by
    rintro c c' ⟨hc1, hc2⟩ ⟨hc1', hc2'⟩
    refine ⟨fun v i h => ?_, fun i v => ?_⟩
    · show c v i + c' v i = 0
      rw [hc1 v i h, hc1' v i h, add_zero]
    · rw [walkSum_add, hc2, hc2', add_zero]
  smul_mem' := by
    rintro r c ⟨hc1, hc2⟩
    refine ⟨fun v i h => ?_, fun i v => ?_⟩
    · show r • c v i = 0
      rw [hc1 v i h, smul_zero]
    · rw [walkSum_smul, hc2, mul_zero]

noncomputable def parCoordFun [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : ↥(parSub Φ R) →ₗ[R] parKer (R := R) Φ where
  toFun ψ := ⟨edgeVal Φ hΦs (ψ : Additive Φ →+ R),
    ⟨fun v i h => edgeVal_tree Φ hΦs _ v i h, (isPar_iff_walkSum Φ hΦs (ψ : Additive Φ →+ R)).mp ψ.2⟩⟩
  map_add' ψ ψ' := Subtype.ext (edgeVal_add Φ hΦs (ψ : Additive Φ →+ R) (ψ' : Additive Φ →+ R))
  map_smul' r ψ := Subtype.ext (edgeVal_smul Φ hΦs r (ψ : Additive Φ →+ R))

theorem parCoordFun_bijective [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : Bijective (parCoordFun (R := R) Φ hΦs) := by
  constructor
  · intro ψ ψ' h
    exact Subtype.ext (edgeVal_injective Φ hΦs (congrArg Subtype.val h))
  · intro c
    have hc1 : ∀ v i, (treeT Φ).tree v i = true → (c : VΦ Φ → Fin 2 → R) v i = 0 := fun v i h => c.2.1 v i h
    have hc2 : ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ (c : VΦ Φ → Fin 2 → R) v (faceWord i (faceLen Φ i v)) = 0 :=
      fun i v => c.2.2 i v
    have hpar : IsPar Φ (charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R)) := by
      rw [isPar_iff_walkSum Φ hΦs, edgeVal_charOfEdge Φ hΦs _ hc1]
      exact hc2
    exact ⟨⟨charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R), hpar⟩, Subtype.ext (edgeVal_charOfEdge Φ hΦs _ hc1)⟩

noncomputable def parCoord [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : ↥(parSub Φ R) ≃ₗ[R] parKer (R := R) Φ :=
  LinearEquiv.ofBijective (parCoordFun Φ hΦs) (parCoordFun_bijective Φ hΦs)

theorem parCoord_apply [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : ↥(parSub Φ R)) :
    ((parCoord Φ hΦs ψ : parKer (R := R) Φ) : VΦ Φ → Fin 2 → R) = edgeVal Φ hΦs (ψ : Additive Φ →+ R) := rfl

end GlueB
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section PairSumIndexed

variable {Γg : Type*} [Group Γg] {R : Type*} [CommRing R]

theorem omega_comm (φ ψ : Additive Γg →+ R) (g h : Γg) : omega φ ψ h g = - omega φ ψ g h := by
  simp only [omega]
  ring

theorem pairSum_eq_sum_fin (φ ψ : Additive Γg →+ R) (L : List Γg) :
    pairSum φ ψ L = ∑ a : Fin L.length, ∑ b : Fin L.length, if a < b then omega φ ψ L[a.1] L[b.1] else 0 := by
  induction L with
  | nil => simp [pairSum]
  | cons g L ih =>
    rw [pairSum, ih]
    show _ = ∑ a : Fin (L.length + 1), ∑ b : Fin (L.length + 1), if a < b then omega φ ψ (g :: L)[a.1] (g :: L)[b.1] else 0
    rw [Fin.sum_univ_succ]
    congr 1
    ·
      rw [Fin.sum_univ_succ]
      simp only [lt_self_iff_false, ↓reduceIte, zero_add, Fin.succ_pos, Fin.val_succ, List.getElem_cons_succ,
        Fin.val_zero, List.getElem_cons_zero]
      exact (Fin.sum_univ_fun_getElem L (omega φ ψ g)).symm
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero, ↓reduceIte, zero_add, Fin.succ_lt_succ_iff, Fin.val_succ, List.getElem_cons_succ]

theorem omega_mul_left' (φ ψ : Additive Γg →+ R) (a b g : Γg) :
    omega φ ψ (a * b) g = omega φ ψ a g + omega φ ψ b g := by
  simp only [omega, ofMul_mul, map_add]
  ring

theorem pairSum_append (φ ψ : Additive Γg →+ R) (L₁ L₂ : List Γg) :
    pairSum φ ψ (L₁ ++ L₂) = pairSum φ ψ L₁ + pairSum φ ψ L₂ + omega φ ψ L₁.prod L₂.prod := by
  induction L₁ with
  | nil => simp [pairSum, omega_one_left]
  | cons g L₁ ih =>
    rw [List.cons_append, pairSum, ih, pairSum, List.prod_cons, omega_mul_left', List.map_append, List.sum_append,
      ← omega_list_prod φ ψ g L₂]
    ring

theorem pairSum_reverse (φ ψ : Additive Γg →+ R) (L : List Γg) : pairSum φ ψ L.reverse = - pairSum φ ψ L := by
  induction L with
  | nil => simp [pairSum]
  | cons g L ih =>
    rw [List.reverse_cons, pairSum_append, ih]
    simp only [pairSum, List.map_nil, List.sum_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
    rw [omega_comm, omega_list_prod, List.map_reverse, List.sum_reverse]
    ring

end PairSumIndexed
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section GlueC

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex]

omit [Φ.FiniteIndex] in

theorem faceVal_pOf [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (i : Fin 3) (v : VΦ Φ) :
    faceVal Φ (hPrim φ ψ) (U i) (pOf Φ i v) = hPrim φ ψ (stabEquiv Φ hΦs (faceElt Φ i v)) := by
  rw [← pmRep_faceElt Φ hΦs]
  rfl

omit [Φ.FiniteIndex] in

theorem mk_pOf_vOf_mem_orbit (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) :
    ((pOf Φ i (vOf Φ hΦs i O) : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers (U i)) ((O.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
  rw [QuotientGroup.out_eq', ← orbitRel_apply]
  apply Quotient.exact
  rw [Quotient.out_eq]
  exact mk_pOf_vOf Φ hΦs i O

theorem pairF_eq_sum_faceElt [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup)
    (φ ψ : Additive Φ →+ R) (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ) :
    pairF Φ φ ψ = ∑ i : Fin 3, ∑ O : OrbitU Φ i, hPrim φ ψ (stabEquiv Φ hΦs (faceElt Φ i (vOf Φ hΦs i O))) := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  have hle : Φ ≤ Gamma 2 := hΦs.trans sanovSubgroup_le_Gamma_two
  have hF_conj : ∀ (c v : Φ), IsParabolicElt v → hPrim φ ψ (c * v * c⁻¹) = hPrim φ ψ v :=
    fun c v hv => hPrim_conj_of_apply_eq_zero φ ψ v (hφ v hv) (hψ v hv) c
  have hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → hPrim φ ψ (v ^ k) = k * hPrim φ ψ v :=
    fun v k _ => hPrim_pow φ ψ v k
  unfold pairF
  rw [cuspSum_eq_two_mul_sum_orbitU Φ hΦ hle (hPrim φ ψ) hF_conj hF_pow, ← mul_assoc, invOf_mul_self, one_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun O _ => ?_
  rw [← faceVal_pOf Φ hΦs φ ψ i (vOf Φ hΦs i O)]
  exact (faceVal_eq_of_same_orbit hΦ (hPrim φ ψ) hF_conj (U i) (sq_trace_U i) _ _ (mk_pOf_vOf_mem_orbit Φ hΦs i O)).symm

noncomputable def letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) : List (Fin 2 × Bool) → List Φ
  | [] => []
  | p :: l => stabEquiv Φ hΦs ((treeT Φ).sx (wprod sanL l • v) p) :: letters hΦs v l

omit [Φ.FiniteIndex] in
theorem prod_letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    (letters Φ hΦs v l).prod = stabEquiv Φ hΦs ((treeT Φ).wordWalk v l) := by
  induction l with
  | nil => rw [letters, List.prod_nil, TreeTransversal.wordWalk_nil, map_one]
  | cons p l ih => rw [letters, List.prod_cons, ih, TreeTransversal.wordWalk_cons, map_mul]

omit [Φ.FiniteIndex] in
theorem length_letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    (letters Φ hΦs v l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [letters, ih]

omit [Φ.FiniteIndex] in

theorem char_letter (hΦs : Φ ≤ sanovSubgroup) (χ : Additive Φ →+ R) (w : VΦ Φ) (p : Fin 2 × Bool) :
    χ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).sx w p))) = sval Φ (edgeVal Φ hΦs χ) w p := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [TreeTransversal.sx_false, map_inv, ofMul_inv, map_neg]
    simp only [sval, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [TreeTransversal.sx_true]
    simp only [sval, ↓reduceIte]
    rfl

omit [Φ.FiniteIndex] in

theorem omega_letter (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w w' : VΦ Φ) (p p' : Fin 2 × Bool) :
    omega φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w p)) (stabEquiv Φ hΦs ((treeT Φ).sx w' p')) =
      sval Φ (edgeVal Φ hΦs φ) w p * sval Φ (edgeVal Φ hΦs ψ) w' p' -
        sval Φ (edgeVal Φ hΦs ψ) w p * sval Φ (edgeVal Φ hΦs φ) w' p' := by
  rw [omega, char_letter, char_letter, char_letter, char_letter]

omit [Φ.FiniteIndex] in

theorem hPrim_letter_false [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (i : Fin 2) :
    hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w (i, false))) =
      - hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx ((sanL i)⁻¹ • w) (i, true))) := by
  rw [TreeTransversal.sx_false, TreeTransversal.sx_true, map_inv, hPrim_inv]

omit [Φ.FiniteIndex] in

theorem hPrim_letter_tree [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (i : Fin 2)
    (h : (treeT Φ).tree w i = true) : hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w (i, true))) = 0 := by
  rw [TreeTransversal.sx_true, (treeT Φ).x_eq_one_of_tree w i h, map_one, hPrim_one]

omit [Φ.FiniteIndex] in

theorem hPrim_wordWalk [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).wordWalk v l)) =
      ((letters Φ hΦs v l).map (hPrim φ ψ)).sum - pairSum φ ψ (letters Φ hΦs v l) := by
  rw [← prod_letters, hPrim_list_prod']

theorem pairF_eq_sum_letters [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup)
    (φ ψ : Additive Φ →+ R) (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ) :
    pairF Φ φ ψ = ∑ i : Fin 3, ∑ O : OrbitU Φ i,
      ((((letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))).map (hPrim φ ψ)).sum -
        pairSum φ ψ (letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))))) := by
  rw [pairF_eq_sum_faceElt Φ hΦs φ ψ hφ hψ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun O _ => ?_
  exact hPrim_wordWalk Φ hΦs φ ψ _ _

end GlueC
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem pairD_swap (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] {R : Type*} [CommRing R]
    [Invertible (2 : R)] [Invertible (6 : R)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) : pairD Λ Γ ψ φ = - pairD Λ Γ φ ψ := by
  unfold pairD
  rw [pairF_swap, mul_neg]

section Assembly

open CongruenceSubgroup

variable {R : Type*} [CommRing R]

private theorem _root_.ModularCurve.PDPairing.TD.cores_cores {K H G' : Subgroup SL(2, ℤ)} (hKH : K ≤ H) (hHG : H ≤ G') [K.FiniteIndex] [H.FiniteIndex]
    (x : Additive K →+ R) :
    cores hHG (cores hKH x) = cores (hKH.trans hHG) x :=
  ModularCurve.PDPairing.T1.cores_cores hKH hHG x

p2m_export "ModularCurve.PDPairing.TD" "cores_cores"
theorem pairF_zero_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (ψ : Additive Φ →+ R) : pairF Φ 0 ψ = 0 := by
  have h := pairF_smul_left Φ (0 : R) (0 : Additive Φ →+ R) ψ
  rwa [zero_smul, zero_mul] at h

theorem pairF_sum_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] {ι : Type*} (S : Finset ι) (f : ι → Additive Φ →+ R) (ψ : Additive Φ →+ R) :
    pairF Φ (∑ i ∈ S, f i) ψ = ∑ i ∈ S, pairF Φ (f i) ψ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pairF_zero_left]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairF_add_left, ih]

def normConj {Φ Γ' : Subgroup SL(2, ℤ)}
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ) (s : Γ') : Φ ≃* Φ where
  toFun g := ⟨(s : SL(2, ℤ))⁻¹ * g * s, by simpa using hnorm s⁻¹ g⟩
  invFun g := ⟨(s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹, hnorm s g⟩
  left_inv g := Subtype.ext (by group)
  right_inv g := Subtype.ext (by group)
  map_mul' g g' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_normConj {Φ Γ' : Subgroup SL(2, ℤ)}
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ) (s : Γ') (g : Φ) :
    ((normConj hnorm s g : Φ) : SL(2, ℤ)) = (s : SL(2, ℤ))⁻¹ * g * s := rfl

theorem pairF_res_cores_normal {Φ Γ' : Subgroup SL(2, ℤ)} (hΦΓ : Φ ≤ Γ') [Φ.FiniteIndex] [Γ'.FiniteIndex]
    [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ)
    (z : Additive Φ →+ R) (y : Additive Γ' →+ R) (hz : IsPar Φ z) (hy : IsPar Γ' y) :
    pairF Φ (res hΦΓ (cores hΦΓ z)) (res hΦΓ y) = (Φ.relIndex Γ' : R) * pairF Φ z (res hΦΓ y) := by
  classical
  set K : Subgroup Γ' := Φ.subgroupOf Γ' with hK
  haveI : Fintype (Γ' ⧸ K) := Fintype.ofFinite _
  let eK : K ≃* Φ := Subgroup.subgroupOfEquivOfLe hΦΓ
  let xK : Additive K →+ R := z.comp (MonoidHom.toAdditive eK.toMonoidHom)
  have hcor : ∀ g : Γ', (cores hΦΓ z) (Additive.ofMul g) =
      coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q) xK g := by
    intro g; rw [coresFun_eq]; rfl

  have htriv : ∀ (g : Φ) (q : Γ' ⧸ K), (Subgroup.inclusion hΦΓ g)⁻¹ • q = q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H s =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      rw [hK, Subgroup.mem_subgroupOf]
      have h := hnorm s⁻¹ g
      simp only [Subgroup.coe_inv, inv_inv] at h
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h

  have hsum : res hΦΓ (cores hΦΓ z) =
      ∑ q : Γ' ⧸ K, z.comp (MonoidHom.toAdditive (normConj hnorm (Quotient.out q)).toMonoidHom) := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    rw [AddMonoidHom.finsetSum_apply]
    show (cores hΦΓ z) (Additive.ofMul (Subgroup.inclusion hΦΓ g)) = _
    rw [hcor, coresFun]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    show z (Additive.ofMul (eK (gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g)))) =
      z (Additive.ofMul (normConj hnorm q.out g))
    congr 2
    apply Subtype.ext
    show (((gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g) : K) : Γ') :
      SL(2, ℤ)) = _
    rw [coe_gam, htriv, coe_normConj]
    rfl
  rw [hsum, pairF_sum_left]
  have hterm : ∀ q : Γ' ⧸ K,
      pairF Φ (z.comp (MonoidHom.toAdditive (normConj hnorm q.out).toMonoidHom)) (res hΦΓ y) =
        pairF Φ z (res hΦΓ y) := by
    intro q
    set s : Γ' := q.out
    have hy' : (res hΦΓ y).comp (MonoidHom.toAdditive (normConj hnorm s).toMonoidHom) = res hΦΓ y := by
      refine AddMonoidHom.ext fun g => ?_
      obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
      show y (Additive.ofMul (Subgroup.inclusion hΦΓ (normConj hnorm s g))) =
        y (Additive.ofMul (Subgroup.inclusion hΦΓ g))
      have : Subgroup.inclusion hΦΓ (normConj hnorm s g) = s⁻¹ * Subgroup.inclusion hΦΓ g * s :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; rfl)
      rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
      ring
    have ht := pairF_transport hΦ1 hΦ1 (normConj hnorm s)
      (((s : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (fun g => by
        rw [coe_normConj]
        have h1 : ((s : SL(2, ℤ)))⁻¹ * (g : SL(2, ℤ)) = ((s : SL(2, ℤ))⁻¹ * g * s) * (s : SL(2, ℤ))⁻¹ := by group
        have h2 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) h1
        simpa only [Matrix.SpecialLinearGroup.coe_mul] using h2)
      z (res hΦΓ y) hz (isPar_res hΦΓ y hy)
    rw [hy'] at ht
    exact ht
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

@[reducible]
noncomputable def invertibleOfDvd48 [Invertible (2 : R)] [Invertible (6 : R)] (n : ℕ) (hn : n ∣ 48) :
    Invertible (n : R) := by
  have hk : 48 = n * (48 / n) := (Nat.mul_div_cancel' hn).symm
  set k : ℕ := 48 / n
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self _
  have h6 : (6 : R) * ⅟6 = 1 := mul_invOf_self _
  have h48 : (48 : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R)) = 1 := by
    linear_combination (6 * ⅟(6 : R) * (4 * ⅟(2 : R) ^ 2 + 2 * ⅟(2 : R) + 1)) * h2 + h6
  have hnk : (n : R) * k = 48 := by
    have h := congrArg (fun t : ℕ => (t : R)) hk
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.symm
  have key : (n : R) * ((k : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R))) = 1 := by rw [← mul_assoc, hnk, h48]
  exact ⟨(k : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R)), by rw [mul_comm]; exact key, key⟩

theorem relIndex_inf_Gamma4_dvd (Γ' : Subgroup SL(2, ℤ)) :
    (Γ' ⊓ Gamma 4).relIndex Γ' ∣ (Gamma 4).index := by
  haveI := Gamma_normal 4
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

private theorem _root_.ModularCurve.PDPairing.TD.index_Gamma_four : (Gamma 4).index = 48 := by
  exact ModularCurve.PDPairing.IDX.index_Gamma_four

p2m_export "ModularCurve.PDPairing.TD" "index_Gamma_four"
noncomputable scoped instance invertibleRelIndexInfGammaFour [Invertible (2 : R)] [Invertible (6 : R)]
    (Γ' : Subgroup SL(2, ℤ)) : Invertible (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) :=
  invertibleOfDvd48 _ (index_Gamma_four ▸ relIndex_inf_Gamma4_dvd Γ')

theorem diag_intertwine (d : ℤ) (g g' : Matrix (Fin 2) (Fin 2) ℤ) (h00 : g' 0 0 = g 0 0) (h01 : g' 0 1 = d * g 0 1)
    (h10 : d * g' 1 0 = g 1 0) (h11 : g' 1 1 = g 1 1) :
    !![d, 0; 0, 1] * g = g' * !![d, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11, mul_comm]

section Aux4Trace
open Matrix Matrix.SpecialLinearGroup

theorem sq_sub_one_eq_zero_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) : (M - 1) ^ 2 = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  ext i j
  rw [sq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination M 0 0 * htr - hdet
      | linear_combination M 0 1 * htr
      | linear_combination M 1 0 * htr
      | linear_combination M 1 1 * htr - hdet

theorem trace_pow_eq_two_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) (n : ℕ) : (M ^ n).trace = 2 := by
  have hNN : (M - 1) * (M - 1) = 0 := by
    rw [← sq]; exact sq_sub_one_eq_zero_of_trace_eq_two M hdet htr
  have hsplit : (1 : Matrix (Fin 2) (Fin 2) ℤ) + (M - 1) = M := by abel
  have hNM : (M - 1) * M = M - 1 := by
    calc (M - 1) * M = (M - 1) * (1 + (M - 1)) := by rw [hsplit]
      _ = (M - 1) * 1 + (M - 1) * (M - 1) := by rw [mul_add]
      _ = M - 1 := by rw [mul_one, hNN, add_zero]
  have hpow : ∀ m : ℕ, M ^ m = 1 + m • (M - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      calc M ^ (k + 1) = M ^ k * M := pow_succ M k
        _ = (1 + k • (M - 1)) * M := by rw [ih]
        _ = 1 * M + (k • (M - 1)) * M := by rw [add_mul]
        _ = M + k • ((M - 1) * M) := by rw [one_mul, smul_mul_assoc]
        _ = M + k • (M - 1) := by rw [hNM]
        _ = 1 + (k + 1) • (M - 1) := by
            rw [succ_nsmul, ← hsplit]
            abel
  rw [hpow n, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, htr, Matrix.trace_one]
  simp [Fintype.card_fin]

theorem sq_trace_pow_eq_four (A : SL(2, ℤ))
    (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) (n : ℕ) :
    (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M.det = 1 := A.2
  have hcoe : (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = M ^ n := by
    simp [hM]
  rw [hcoe]
  have htr : M.trace = 2 ∨ M.trace = -2 := by
    have h0 : (M.trace - 2) * (M.trace + 2) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases htr with h2 | hm2
  · rw [trace_pow_eq_two_of_trace_eq_two M hdet h2 n]; norm_num
  · have hdetneg : (-M).det = 1 := by
      rw [Matrix.det_neg]
      simp [hdet, Fintype.card_fin]
    have htrneg : (-M).trace = 2 := by rw [Matrix.trace_neg, hm2]; ring
    have hkey := trace_pow_eq_two_of_trace_eq_two (-M) hdetneg htrneg n
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_pow] at hkey
      rw [hkey]; norm_num
    · rw [ho.neg_pow, Matrix.trace_neg] at hkey
      have hm : (M ^ n).trace = -2 := by linarith
      rw [hm]; norm_num

variable (R : Type*) [CommRing R] (M M' d : ℕ)

theorem trace_conj_SL (b c : SL(2, ℤ)) :
    ((b⁻¹ * c * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_comm, ← mul_assoc, ← coe_mul, mul_inv_cancel,
    coe_one, one_mul]

end Aux4Trace
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem cores_smul {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (r : R) (x : Additive Φ' →+ R) :
    cores h (r • x) = r • cores h x := by
  classical
  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Φ ⧸ K) := Fintype.ofFinite _
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  have e1 : (cores h (r • x)) (Additive.ofMul g) = coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q)
      ((r • x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom)) g := by
    rw [coresFun_eq]; rfl
  have e2 : (cores h x) (Additive.ofMul g) = coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q)
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom)) g := by
    rw [coresFun_eq]; rfl
  rw [AddMonoidHom.smul_apply, e1, e2, coresFun, coresFun, smul_eq_mul, Finset.mul_sum]
  rfl

theorem isPar_cores {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (x : Additive Φ' →+ R)
    (hx : IsPar Φ' x) : IsPar Φ (cores h x) := by
  classical
  intro u hu
  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (Φ ⧸ K))) := Fintype.ofFinite _
  let e : K ≃* Φ' := Subgroup.subgroupOfEquivOfLe h
  let xK : Additive K →+ R := x.comp (MonoidHom.toAdditive e.toMonoidHom)
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight xK) u) = 0
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero (fun o _ => ?_)
  show x (Additive.ofMul (e ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩)) = 0
  apply hx
  show ((((o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out : Φ)) : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_SL]
  exact sq_trace_pow_eq_four (u : SL(2, ℤ)) hu _

theorem isPar_comp_equiv {Γ' Φ'' : Subgroup SL(2, ℤ)} (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (ha : a.det ≠ 0)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (x' : Additive Γ' →+ R) (hx' : IsPar Γ' x') :
    IsPar Φ'' (x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom)) := by
  intro g hg
  show x' (Additive.ofMul (e.symm g)) = 0
  apply hx'
  have h1 := he (e.symm g)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [← trace_intertwine a _ _ ha h1]
  exact hg

theorem isPar_comp_equiv' {Γ' Φ'' : Subgroup SL(2, ℤ)} (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (ha : a.det ≠ 0)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (y : Additive Φ'' →+ R) (hy : IsPar Φ'' y) :
    IsPar Γ' (y.comp (MonoidHom.toAdditive e.toMonoidHom)) := by
  intro g hg
  show y (Additive.ofMul (e g)) = 0
  apply hy
  rw [trace_intertwine a _ _ ha (he g)]
  exact hg

theorem res_res {Φ₁ Φ₂ Φ₃ : Subgroup SL(2, ℤ)} (h₁₂ : Φ₁ ≤ Φ₂) (h₂₃ : Φ₂ ≤ Φ₃) (y : Additive Φ₃ →+ R) :
    res h₁₂ (res h₂₃ y) = res (h₁₂.trans h₂₃) y :=
  AddMonoidHom.ext fun _ => rfl

theorem res_smul {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (r : R) (y : Additive Φ →+ R) :
    res h (r • y) = r • res h y :=
  AddMonoidHom.ext fun _ => rfl

theorem neg_one_not_mem_Gamma_four : (-1 : SL(2, ℤ)) ∉ Gamma 4 := by
  intro h
  rw [Gamma_mem] at h
  have h00 := h.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq, Int.cast_neg, Int.cast_one] at h00
  revert h00
  decide

theorem pairD_cores_transport [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    {Γ' Γ'' Φ'' P Q : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex] [Γ''.FiniteIndex] [Φ''.FiniteIndex]
    [(Γ' ⊓ Gamma 4 ⊓ P).FiniteIndex] [(Φ'' ⊓ Gamma 4 ⊓ Q).FiniteIndex]
    (hΦ : Φ'' ≤ Γ'') (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (hP : ∀ g : Γ', (g : SL(2, ℤ)) ∈ Gamma 4 → ((g : SL(2, ℤ)) ∈ P ↔ ((e g : Φ'') : SL(2, ℤ)) ∈ Gamma 4))
    (hQ : ∀ h : Φ'', (h : SL(2, ℤ)) ∈ Gamma 4 → ((h : SL(2, ℤ)) ∈ Q ↔ ((e.symm h : Γ') : SL(2, ℤ)) ∈ Gamma 4))
    [Invertible (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)] [Invertible (((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R)]
    [Invertible (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)]
    [Invertible (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R)]
    (x' : Additive Γ' →+ R) (y : Additive Γ'' →+ R) (hx' : IsPar Γ' x') (hy : IsPar Γ'' y) :
    pairD (Gamma 4) Γ'' (cores hΦ (x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom))) y =
      pairD (Gamma 4) Γ' x' ((res hΦ y).comp (MonoidHom.toAdditive e.toMonoidHom)) := by
  classical
  haveI hΔn := Gamma_normal 4
  have hΔ1 : (-1 : SL(2, ℤ)) ∉ Gamma 4 := neg_one_not_mem_Gamma_four

  have hΦΓ : Γ'' ⊓ Gamma 4 ≤ Γ'' := inf_le_left
  have h₃ : Φ'' ⊓ Gamma 4 ≤ Φ'' := inf_le_left
  have h₃Φ : Φ'' ⊓ Gamma 4 ≤ Γ'' ⊓ Gamma 4 := inf_le_inf_right (Gamma 4) hΦ
  have h₃Γ : Φ'' ⊓ Gamma 4 ≤ Γ'' := h₃.trans hΦ
  have h₁' : Γ' ⊓ Gamma 4 ≤ Γ' := inf_le_left
  have hΦ₁ : Γ' ⊓ Gamma 4 ⊓ P ≤ Γ' ⊓ Gamma 4 := inf_le_left
  have hΦ₁Γ : Γ' ⊓ Gamma 4 ⊓ P ≤ Γ' := hΦ₁.trans h₁'
  have h₂₃ : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Φ'' ⊓ Gamma 4 := inf_le_left
  have h₂'' : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Φ'' := h₂₃.trans h₃
  have h₂Γ : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Γ'' := h₂''.trans hΦ
  haveI : IsFreeGroup ↥(Γ' ⊓ Gamma 4 ⊓ P) :=
    IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (hΦ₁.trans inf_le_right : Γ' ⊓ Gamma 4 ⊓ P ≤ Gamma 4))
  haveI : IsFreeGroup ↥(Φ'' ⊓ Gamma 4 ⊓ Q) :=
    IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (h₂₃.trans inf_le_right : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Gamma 4))
  have hane : a.det ≠ 0 := ne_of_gt ha

  set x'' : Additive Φ'' →+ R := x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom) with hx''def
  have hx'' : IsPar Φ'' x'' := isPar_comp_equiv e a hane he x' hx'
  set y' : Additive Γ' →+ R := (res hΦ y).comp (MonoidHom.toAdditive e.toMonoidHom) with hy'def
  have hy' : IsPar Γ' y' := isPar_comp_equiv' e a hane he (res hΦ y) (isPar_res hΦ y hy)

  set PP : R := pairF (Φ'' ⊓ Gamma 4) (res h₃ x'') (res h₃Γ y) with hPP

  have hm_eq : x'' = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) • cores h₃ (res h₃ x'') := by
    rw [cores_res h₃ x'', smul_smul, invOf_mul_self, one_smul]
  have hL1 : cores hΦ x'' = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) •
      cores hΦΓ (cores h₃Φ (res h₃ x'')) := by
    conv_lhs => rw [hm_eq]
    rw [cores_smul, cores_cores h₃ hΦ, ← cores_cores h₃Φ hΦΓ]
  have hz : IsPar (Γ'' ⊓ Gamma 4) (cores h₃Φ (res h₃ x'')) := isPar_cores h₃Φ _ (isPar_res h₃ x'' hx'')
  have hnorm : ∀ (s : Γ'') (g : ↥(Γ'' ⊓ Gamma 4)),
      (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Γ'' ⊓ Gamma 4 := fun s g =>
    ⟨Γ''.mul_mem (Γ''.mul_mem s.2 g.2.1) (Γ''.inv_mem s.2), hΔn.conj_mem _ g.2.2 _⟩
  have hΦ1 : (-1 : SL(2, ℤ)) ∉ Γ'' ⊓ Gamma 4 := fun h => hΔ1 h.2
  have hLHS : pairD (Gamma 4) Γ'' (cores hΦ x'') y = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * PP := by
    show ⅟(((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) *
        pairF (Γ'' ⊓ Gamma 4) (res hΦΓ (cores hΦ x'')) (res hΦΓ y) = _
    rw [hL1, res_smul, pairF_smul_left, pairF_res_cores_normal hΦΓ hΦ1 hnorm _ y hz hy,
      pairF_cores_left h₃Φ (res h₃ x'') (res hΦΓ y) (isPar_res h₃ x'' hx'') (isPar_res hΦΓ y hy), res_res, hPP]
    have hn : ⅟(((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) * (((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) = 1 :=
      invOf_mul_self _
    linear_combination (⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) *
      pairF (Φ'' ⊓ Gamma 4) (res h₃ x'') (res h₃Γ y)) * hn

  have memP : ∀ g : ↥(Γ' ⊓ Gamma 4 ⊓ P), ((e ⟨g, g.2.1.1⟩ : Φ'') : SL(2, ℤ)) ∈ Φ'' ⊓ Gamma 4 ⊓ Q := by
    intro g
    have hg4 : ((e ⟨g, g.2.1.1⟩ : Φ'') : SL(2, ℤ)) ∈ Gamma 4 := (hP ⟨g, g.2.1.1⟩ g.2.1.2).mp g.2.2
    exact ⟨⟨(e ⟨g, g.2.1.1⟩).2, hg4⟩,
      (hQ (e ⟨g, g.2.1.1⟩) hg4).mpr (by rw [MulEquiv.symm_apply_apply]; exact g.2.1.2)⟩
  have memQ : ∀ h : ↥(Φ'' ⊓ Gamma 4 ⊓ Q), ((e.symm ⟨h, h.2.1.1⟩ : Γ') : SL(2, ℤ)) ∈ Γ' ⊓ Gamma 4 ⊓ P := by
    intro h
    have hh4 : ((e.symm ⟨h, h.2.1.1⟩ : Γ') : SL(2, ℤ)) ∈ Gamma 4 := (hQ ⟨h, h.2.1.1⟩ h.2.1.2).mp h.2.2
    exact ⟨⟨(e.symm ⟨h, h.2.1.1⟩).2, hh4⟩,
      (hP (e.symm ⟨h, h.2.1.1⟩) hh4).mpr (by rw [MulEquiv.apply_symm_apply]; exact h.2.1.2)⟩
  let e₁ : ↥(Γ' ⊓ Gamma 4 ⊓ P) ≃* ↥(Φ'' ⊓ Gamma 4 ⊓ Q) :=
    { toFun := fun g => ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), memP g⟩
      invFun := fun h => ⟨(e.symm ⟨h, h.2.1.1⟩ : SL(2, ℤ)), memQ h⟩
      left_inv := fun g => by
        apply Subtype.ext
        show ((e.symm ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), (e ⟨g, g.2.1.1⟩).2⟩ : Γ') : SL(2, ℤ)) = g
        rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
      right_inv := fun h => by
        apply Subtype.ext
        show ((e ⟨(e.symm ⟨h, h.2.1.1⟩ : SL(2, ℤ)), (e.symm ⟨h, h.2.1.1⟩).2⟩ : Φ'') : SL(2, ℤ)) = h
        rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      map_mul' := fun g g' => by
        apply Subtype.ext
        calc ((e ⟨(g * g' : ↥(Γ' ⊓ Gamma 4 ⊓ P)), (g * g').2.1.1⟩ : Φ'') : SL(2, ℤ))
            = ((e (⟨g, g.2.1.1⟩ * ⟨g', g'.2.1.1⟩) : Φ'') : SL(2, ℤ)) := rfl
          _ = ((e ⟨g, g.2.1.1⟩ * e ⟨g', g'.2.1.1⟩ : Φ'') : SL(2, ℤ)) := by rw [map_mul]
          _ = (e ⟨g, g.2.1.1⟩ : SL(2, ℤ)) * (e ⟨g', g'.2.1.1⟩ : SL(2, ℤ)) := rfl }
  have he₁ : ∀ g : ↥(Γ' ⊓ Gamma 4 ⊓ P), a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e₁ g : ↥(Φ'' ⊓ Gamma 4 ⊓ Q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := fun g => he ⟨g, g.2.1.1⟩
  have hΦ₁1 : (-1 : SL(2, ℤ)) ∉ Γ' ⊓ Gamma 4 ⊓ P := fun h => hΔ1 h.1.2
  have hΦ₂1 : (-1 : SL(2, ℤ)) ∉ Φ'' ⊓ Gamma 4 ⊓ Q := fun h => hΔ1 h.1.2

  have hT := pairF_transport hΦ₁1 hΦ₂1 e₁ a ha he₁ (res h₂'' x'') (res h₂Γ y)
    (isPar_res h₂'' x'' hx'') (isPar_res h₂Γ y hy)
  have hxe : (res h₂'' x'').comp (MonoidHom.toAdditive e₁.toMonoidHom) = res hΦ₁Γ x' := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Γ' ⊓ Gamma 4 ⊓ P), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    show x' (Additive.ofMul (e.symm ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), (memP g).1.1⟩)) =
      x' (Additive.ofMul ⟨g, g.2.1.1⟩)
    rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  have hye : (res h₂Γ y).comp (MonoidHom.toAdditive e₁.toMonoidHom) = res hΦ₁Γ y' := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Γ' ⊓ Gamma 4 ⊓ P), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    show y (Additive.ofMul (⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), h₂Γ (memP g)⟩ : Γ'')) =
      y (Additive.ofMul (Subgroup.inclusion hΦ (e ⟨g, g.2.1.1⟩)))
    rfl
  rw [hxe, hye] at hT

  have hR1 := pairF_res_res hΦ₁ (res h₁' x') (res h₁' y') (isPar_res h₁' x' hx') (isPar_res h₁' y' hy')
  rw [res_res, res_res] at hR1

  have hR3 := pairF_res_res h₂₃ (res h₃ x'') (res h₃Γ y) (isPar_res h₃ x'' hx'') (isPar_res h₃Γ y hy)
  rw [res_res, res_res] at hR3

  have hRHS : pairD (Gamma 4) Γ' x' y' =
      ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        ((((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * PP)) := by
    show ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * pairF (Γ' ⊓ Gamma 4) (res h₁' x') (res h₁' y') = _
    congr 1
    have hm₁ : ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) = 1 := invOf_mul_self _
    rw [← hR3, ← hT, hR1, ← mul_assoc, hm₁, one_mul]

  have hmap : (Φ'' ⊓ Gamma 4 ⊓ Q).subgroupOf Φ'' = ((Γ' ⊓ Gamma 4 ⊓ P).subgroupOf Γ').map (e : Γ' →* Φ'') := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hh
      refine ⟨e.symm h, ?_, MulEquiv.apply_symm_apply e h⟩
      rw [Subgroup.mem_subgroupOf]
      exact memQ ⟨h, hh⟩
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hg
      exact memP ⟨g, hg⟩
  have hidx : (Γ' ⊓ Gamma 4 ⊓ P).relIndex Γ' = (Φ'' ⊓ Gamma 4 ⊓ Q).relIndex Φ'' := by
    rw [Subgroup.relIndex, Subgroup.relIndex, hmap]
    exact (Subgroup.index_map_equiv ((Γ' ⊓ Gamma 4 ⊓ P).subgroupOf Γ') e).symm
  have key : ((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4)) * ((Γ' ⊓ Gamma 4).relIndex Γ') =
      ((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4)) * ((Φ'' ⊓ Gamma 4).relIndex Φ'') := by
    rw [Subgroup.relIndex_mul_relIndex (Γ' ⊓ Gamma 4 ⊓ P) (Γ' ⊓ Gamma 4) Γ' hΦ₁ h₁',
      Subgroup.relIndex_mul_relIndex (Φ'' ⊓ Gamma 4 ⊓ Q) (Φ'' ⊓ Gamma 4) Φ'' h₂₃ h₃, hidx]
  have hcast : (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) =
      (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by
    have h := congrArg (fun t : ℕ => (t : R)) key
    simpa only [Nat.cast_mul] using h
  have step : ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
      (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by
    have hA : ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) = 1 :=
      invOf_mul_self _
    have hB : ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) = 1 := invOf_mul_self _
    have hC : (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) = 1 :=
      mul_invOf_self _
    calc ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R)
        = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) *
            ((((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)) := by
            rw [hC, mul_one]
      _ = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          ((((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by ring
      _ = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          ((((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by rw [hcast]
      _ = (⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)) *
          (⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
            (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by ring
      _ = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by rw [hA, hB, one_mul, one_mul]
  rw [hLHS, hRHS, ← mul_assoc, ← mul_assoc, step]

theorem hecke_coset_symm (N : ℕ) (ℓ : ℕ) (hℓN : Nat.Coprime ℓ N) :
    ∃ γ₁ γ₂ : SL(2, ℤ), γ₁ ∈ Gamma0 N ∧ γ₂ ∈ Gamma0 N ∧
      (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by

  obtain ⟨u, v, huv⟩ : IsCoprime (ℓ : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hℓN

  refine ⟨⟨!![(ℓ : ℤ) * u, v; -(N : ℤ), 1], ?_⟩, ⟨!![(ℓ : ℤ), -v; (N : ℤ), u], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [Gamma0_mem]
    show (((-(N : ℤ)) : ℤ) : ZMod N) = 0
    simp
  · rw [Gamma0_mem]
    show (((N : ℤ) : ℤ) : ZMod N) = 0
    simp
  · show (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(ℓ : ℤ) * u, v; -(N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), -v; (N : ℤ), u]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (ℓ : ℤ) * huv
        | linear_combination (-(ℓ : ℤ)) * huv
        | linear_combination huv
        | linear_combination (-1 : ℤ) * huv
        | ring1

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section DescentPerfect

open CongruenceSubgroup

variable {R : Type*} [CommRing R]

theorem cores_add {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (x y : Additive Φ' →+ R) :
    cores h (x + y) = cores h x + cores h y := by
  unfold cores
  rw [AddMonoidHom.add_comp, toMultiplicativeRight_add, transfer_mul,
    toAdditiveLeft_mul]

noncomputable def coresPar {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] :
    ↥(parSub Φ' R) →ₗ[R] ↥(parSub Φ R) where
  toFun ψ := ⟨cores h (ψ : Additive Φ' →+ R), isPar_cores h _ ψ.2⟩
  map_add' _ _ := Subtype.ext (cores_add h _ _)
  map_smul' r _ := Subtype.ext (cores_smul h r _)

theorem pairD_perfect (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] [Λ.Normal]
    (hΛ1 : (-1 : SL(2, ℤ)) ∉ Λ) [Invertible (2 : R)] [Invertible (6 : R)]
    [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (hF : ∀ l' : ↥(parSub (Γ ⊓ Λ) R) →ₗ[R] R, ∃! φ₀' : ↥(parSub (Γ ⊓ Λ) R), ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
      pairF (Γ ⊓ Λ) (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R) (ψ' : Additive ↥(Γ ⊓ Λ) →+ R) = l' ψ')
    (l : ↥(parSub Γ R) →ₗ[R] R) :
    ∃! φ₀ : ↥(parSub Γ R), ∀ ψ : ↥(parSub Γ R), pairD Λ Γ (φ₀ : Additive Γ →+ R) (ψ : Additive Γ →+ R) = l ψ := by
  have hΦΓ : Γ ⊓ Λ ≤ Γ := inf_le_left
  have hΦ1 : (-1 : SL(2, ℤ)) ∉ Γ ⊓ Λ := fun h => hΛ1 h.2
  have hnorm : ∀ (s : Γ) (g : ↥(Γ ⊓ Λ)), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Γ ⊓ Λ := fun s g =>
    ⟨Γ.mul_mem (Γ.mul_mem s.2 g.2.1) (Γ.inv_mem s.2), Subgroup.Normal.conj_mem inferInstance _ g.2.2 _⟩
  have hinv : ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) = 1 := invOf_mul_self _

  let l' : ↥(parSub (Γ ⊓ Λ) R) →ₗ[R] R := ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • (l.comp (coresPar hΦΓ))
  have hl' : ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
      l' ψ' = ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * l ⟨cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ ψ'.2⟩ :=
    fun ψ' => rfl
  obtain ⟨φ₀', hφ₀', huniq'⟩ := hF l'
  refine ⟨⟨cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ φ₀'.2⟩, ?_, ?_⟩
  · intro ψ
    show ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) *
        pairF (Γ ⊓ Λ) (res hΦΓ (cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R))) (res hΦΓ (ψ : Additive Γ →+ R)) = l ψ
    rw [pairF_res_cores_normal hΦΓ hΦ1 hnorm _ _ φ₀'.2 ψ.2, ← mul_assoc, hinv, one_mul,
      hφ₀' ⟨res hΦΓ (ψ : Additive Γ →+ R), isPar_res hΦΓ _ ψ.2⟩, hl']
    have hc : (⟨cores hΦΓ (res hΦΓ (ψ : Additive Γ →+ R)), isPar_cores hΦΓ _ (isPar_res hΦΓ _ ψ.2)⟩ : ↥(parSub Γ R)) =
        (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • ψ :=
      Subtype.ext (cores_res hΦΓ (ψ : Additive Γ →+ R))
    rw [hc, map_smul, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  · intro φ₁ hφ₁

    have key : ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
        pairF (Γ ⊓ Λ) (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • res hΦΓ (φ₁ : Additive Γ →+ R))
          (ψ' : Additive ↥(Γ ⊓ Λ) →+ R) = l' ψ' := by
      intro ψ'
      have h2 := hφ₁ ⟨cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ ψ'.2⟩
      have h3 : pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) (res hΦΓ (cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R))) =
          (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) ψ' := by
        rw [pairF_swap, pairF_res_cores_normal hΦΓ hΦ1 hnorm _ _ ψ'.2 φ₁.2, pairF_swap, mul_neg, neg_neg]
      rw [pairF_smul_left, hl', ← h2]
      show _ = ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) *
        pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) (res hΦΓ (cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R))))
      rw [h3, ← mul_assoc (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R)) (((Γ ⊓ Λ).relIndex Γ : ℕ) : R), hinv, one_mul]
    have hres : (⟨⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • res hΦΓ (φ₁ : Additive Γ →+ R),
        (parSub (Γ ⊓ Λ) R).smul_mem _ (isPar_res hΦΓ _ φ₁.2)⟩ : ↥(parSub (Γ ⊓ Λ) R)) = φ₀' := huniq' _ key
    apply Subtype.ext
    show (φ₁ : Additive Γ →+ R) = cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R)
    have h4 : cores hΦΓ (res hΦΓ (φ₁ : Additive Γ →+ R)) = (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • (φ₁ : Additive Γ →+ R) :=
      cores_res hΦΓ _
    have h5 : cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R) =
        ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • cores hΦΓ (res hΦΓ (φ₁ : Additive Γ →+ R)) := by
      rw [← hres, ← cores_smul]
    rw [h5, h4, smul_smul, hinv, one_smul]

end DescentPerfect
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section Inst

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

variable {R : Type*} [CommRing R]

theorem transfer_eq_of_eq {G A : Type*} [Group G] [CommGroup A] {K₁ K₂ : Subgroup G} [K₁.FiniteIndex]
    [K₂.FiniteIndex] (hK : K₁ = K₂) (χ₁ : K₁ →* A) (χ₂ : K₂ →* A)
    (hχ : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂), χ₁ ⟨g, h₁⟩ = χ₂ ⟨g, h₂⟩) :
    MonoidHom.transfer χ₁ = MonoidHom.transfer χ₂ := by
  subst hK
  have : χ₁ = χ₂ := MonoidHom.ext fun x => hχ x x.2 x.2
  subst this
  rfl

section InstPD3

variable (M M' d : ℕ) [NeZero M] [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)

def PhiDeg : Subgroup SL(2, ℤ) := ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd).range).map (Gamma0 M).subtype

omit [NeZero M] [NeZero M'] in
theorem PhiDeg_le : PhiDeg M M' d hMM' hdd ≤ Gamma0 M := Subgroup.map_subtype_le _

noncomputable def eDeg : ↥(Gamma0 M') ≃* ↥(PhiDeg M M' d hMM' hdd) :=
  (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd)).trans
    (Subgroup.equivMapOfInjective _ (Gamma0 M).subtype (Gamma0 M).subtype_injective)

omit [NeZero M] [NeZero M'] in
theorem coe_eDeg (g : ↥(Gamma0 M')) :
    ((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) =
      ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) := by
  show ((Subgroup.equivMapOfInjective _ (Gamma0 M).subtype (Gamma0 M).subtype_injective
    (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd) g) : ↥(PhiDeg M M' d hMM' hdd)) :
      SL(2, ℤ)) = _
  rw [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_subtype, MonoidHom.ofInjective_apply]

omit [NeZero M] [NeZero M'] in
theorem iotaDeg0_entries (g : ↥(Gamma0 M')) :
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 0 0 = (g : SL(2, ℤ)) 0 0 ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 0 1 = (g : SL(2, ℤ)) 0 1 * d ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 1 0 = (g : SL(2, ℤ)) 1 0 / d ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 1 1 = (g : SL(2, ℤ)) 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ModularCurve.PDPairing.iotaDeg0, ModularCurve.PDPairing.conjLowerMat]

omit [NeZero M] [NeZero M'] in

theorem eDeg_intertwine (g : ↥(Gamma0 M')) :
    !![(d : ℤ), 0; 0, 1] * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        !![(d : ℤ), 0; 0, 1] := by
  rw [coe_eDeg]
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
  refine diag_intertwine d _ _ e00 (by rw [e01, mul_comm]) ?_ e11
  rw [e10]
  exact Int.mul_ediv_cancel' (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)

omit [NeZero M] [NeZero M'] in

theorem iDeg0_eq (y : Additive ↥(Gamma0 M) →+ R) :
    ModularCurve.PDPairing.iDeg0 M M' d R R hMM' hdd y =
      (res (PhiDeg_le M M' d hMM' hdd) y).comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).toMonoidHom) := by
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Gamma0 M'), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  show y (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g)) =
    y (Additive.ofMul (Subgroup.inclusion (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd g)))
  have : ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g =
      Subgroup.inclusion (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd g) :=
    Subtype.ext (coe_eDeg M M' d hMM' hdd g).symm
  rw [this]

omit [NeZero M] in

theorem Gamma_le_PhiDeg : Gamma (M' * d) ≤ PhiDeg M M' d hMM' hdd := by
  intro g hg
  have hg0 : g ∈ Gamma0 M := by
    rw [Gamma0_mem]
    rw [Gamma_mem] at hg
    obtain ⟨_, _, h10, _⟩ := hg
    have hdvd : ((M' * d : ℕ) : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine dvd_trans ?_ hdvd
    have hM : (M : ℤ) ∣ (M' : ℤ) := by exact_mod_cast hMM'
    exact dvd_trans hM (by push_cast; exact Dvd.intro _ rfl)
  have hr := ModularCurve.PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 M M' d hMM' hdd
    (show (⟨g, hg0⟩ : ↥(Gamma0 M)) ∈ (Gamma (M' * d)).subgroupOf (Gamma0 M) from hg)
  exact ⟨⟨g, hg0⟩, hr, rfl⟩

scoped instance PhiDeg_finiteIndex : (PhiDeg M M' d hMM' hdd).FiniteIndex :=
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  Subgroup.finiteIndex_of_le (Gamma_le_PhiDeg M M' d hMM' hdd)

omit [NeZero M] in

theorem jDeg0_eq (x' : Additive ↥(Gamma0 M') →+ R) :
    ModularCurve.PDPairing.jDeg0 M M' d R R hMM' hdd x' =
      cores (PhiDeg_le M M' d hMM' hdd) (x'.comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).symm.toMonoidHom)) := by
  have hK : (PhiDeg M M' d hMM' hdd).subgroupOf (Gamma0 M) = (ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd).range :=
    Subgroup.comap_map_eq_self_of_injective (Gamma0 M).subtype_injective _
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 M M' d R hMM' hdd x'))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      ((x'.comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).symm.toMonoidHom)).comp
        (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd)).toMonoidHom))))
  congr 1
  refine transfer_eq_of_eq hK.symm _ _ (fun g h₁ h₂ => ?_)

  show Multiplicative.ofAdd (x' (Additive.ofMul
      ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd)).symm ⟨g, h₁⟩))) =
    Multiplicative.ofAdd (x' (Additive.ofMul ((eDeg M M' d hMM' hdd).symm
      (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd) ⟨g, h₂⟩))))
  congr 3
  apply ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd
  apply Subtype.ext
  rw [MonoidHom.apply_ofInjective_symm]
  have h3 := coe_eDeg M M' d hMM' hdd ((eDeg M M' d hMM' hdd).symm
    (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd) ⟨g, h₂⟩))
  rw [MulEquiv.apply_symm_apply] at h3
  rw [← h3]
  rfl

end InstPD3
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem relIndex_Gamma0_four_mul_dvd_four (M' d : ℕ) [NeZero M'] [NeZero d] (hd : d ∣ M') :
    (Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).relIndex (Gamma0 M' ⊓ Gamma 4) ∣ 4 := by
  classical
  haveI : NeZero (4 * d) := ⟨mul_ne_zero four_ne_zero (NeZero.ne d)⟩
  have h4d : ((4 * d : ℕ) : ℤ) = 4 * (d : ℤ) := by push_cast; ring
  have hdM : (d : ℤ) ∣ (M' : ℤ) := by exact_mod_cast hd
  have hc : ∀ g : ↥(Gamma0 M' ⊓ Gamma 4), (d : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := fun g =>
    dvd_trans hdM ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.2.1))
  have hmul : ∀ g g' : ↥(Gamma0 M' ⊓ Gamma 4),
      ((4 * d : ℕ) : ℤ) ∣ ((g * g' : ↥(Gamma0 M' ⊓ Gamma 4)) : SL(2, ℤ)) 1 0 -
        ((g : SL(2, ℤ)) 1 0 + (g' : SL(2, ℤ)) 1 0) := by
    intro g g'
    have ha' : (4 : ℤ) ∣ (g' : SL(2, ℤ)) 0 0 - 1 := by
      have h := (Gamma_mem.mp g'.2.2).1
      have h' : (((g' : SL(2, ℤ)) 0 0 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by rw [h, Int.cast_one]
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp h')
    have hd₀ : (4 : ℤ) ∣ (g : SL(2, ℤ)) 1 1 - 1 := by
      have h := (Gamma_mem.mp g.2.2).2.2.2
      have h' : (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by rw [h, Int.cast_one]
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp h')
    have hprod : ((g * g' : ↥(Gamma0 M' ⊓ Gamma 4)) : SL(2, ℤ)) 1 0 =
        (g : SL(2, ℤ)) 1 0 * (g' : SL(2, ℤ)) 0 0 + (g : SL(2, ℤ)) 1 1 * (g' : SL(2, ℤ)) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hprod, h4d]
    have e : (g : SL(2, ℤ)) 1 0 * (g' : SL(2, ℤ)) 0 0 + (g : SL(2, ℤ)) 1 1 * (g' : SL(2, ℤ)) 1 0 -
        ((g : SL(2, ℤ)) 1 0 + (g' : SL(2, ℤ)) 1 0) =
      (g : SL(2, ℤ)) 1 0 * ((g' : SL(2, ℤ)) 0 0 - 1) + ((g : SL(2, ℤ)) 1 1 - 1) * (g' : SL(2, ℤ)) 1 0 := by ring
    rw [e]
    refine dvd_add ?_ ?_
    · rw [mul_comm (4 : ℤ)]; exact mul_dvd_mul (hc g) ha'
    · exact mul_dvd_mul hd₀ (hc g')
  let f : ↥(Gamma0 M' ⊓ Gamma 4) →* Multiplicative (ZMod (4 * d)) :=
    { toFun := fun g => Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d)))
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [← ofAdd_add, ← Int.cast_add]
        congr 1
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (hmul g g') }
  have hker : (Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).subgroupOf (Gamma0 M' ⊓ Gamma 4) = f.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    show (g : SL(2, ℤ)) ∈ Gamma0 M' ⊓ Gamma 4 ∧ (g : SL(2, ℤ)) ∈ Gamma0 (4 * d) ↔
      Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d))) = 1
    rw [Gamma0_mem, ofAdd_eq_one]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  have hrange : f.range ≤ Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d))) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hc g
    refine ⟨k, ?_⟩
    show Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)) ^ k =
      Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d)))
    rw [hk, ← ofAdd_zsmul, zsmul_eq_mul, Int.cast_mul]
    exact congrArg Multiplicative.ofAdd (mul_comm _ _)
  have hcard : Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)))) = 4 := by
    rw [Nat.card_zpowers, orderOf_ofAdd_eq_addOrderOf, Int.cast_natCast,
      ZMod.addOrderOf_coe d (mul_ne_zero four_ne_zero (NeZero.ne d)), Nat.gcd_eq_right (dvd_mul_left d 4),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne d))]
  calc Nat.card f.range ∣ Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)))) :=
        Subgroup.card_dvd_of_le hrange
    _ = 4 := hcard

theorem pairD_jDeg0_iDeg0 [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    (M M' d : ℕ) [NeZero M] [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (x' : Additive ↥(Gamma0 M') →+ R) (y : Additive ↥(Gamma0 M) →+ R)
    (hx' : IsParabolicHom (Gamma0 M') x') (hy : IsParabolicHom (Gamma0 M) y) :
    pairD (Gamma 4) (Gamma0 M) (ModularCurve.PDPairing.jDeg0 M M' d R R hMM' hdd x') y =
      pairD (Gamma 4) (Gamma0 M') x' (ModularCurve.PDPairing.iDeg0 M M' d R R hMM' hdd y) := by
  haveI : NeZero (4 * d) := ⟨mul_ne_zero four_ne_zero (NeZero.ne d)⟩

  haveI : Invertible (((Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).relIndex (Gamma0 M' ⊓ Gamma 4) : ℕ) : R) :=
    invertibleOfDvd48 _ (dvd_trans (relIndex_Gamma0_four_mul_dvd_four M' d
      (dvd_trans hdd (Nat.div_dvd_of_dvd hMM'))) (by norm_num))
  haveI : (ModularCurve.PDPairing.Gamma0Upper (4 * d)).FiniteIndex := inferInstance

  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hP : ∀ g : ↥(Gamma0 M'), (g : SL(2, ℤ)) ∈ Gamma 4 →
      ((g : SL(2, ℤ)) ∈ Gamma0 (4 * d) ↔
        ((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) ∈ Gamma 4) := by
    intro g hg4
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
    rw [coe_eDeg, Gamma0_mem, Gamma_mem, e00, e01, e10, e11, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Gamma_mem] at hg4
    obtain ⟨h00, h01, h10, h11⟩ := hg4
    have hb : ((((g : SL(2, ℤ)) 0 1 * d : ℤ)) : ZMod 4) = 0 := by push_cast; rw [h01, zero_mul]
    constructor
    · intro hc
      refine ⟨h00, hb, ?_, h11⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)]
      have : ((4 * d : ℕ) : ℤ) = (d : ℤ) * 4 := by push_cast; ring
      rwa [this] at hc
    · rintro ⟨-, -, hc, -⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)] at hc
      have : ((4 * d : ℕ) : ℤ) = (d : ℤ) * 4 := by push_cast; ring
      rwa [this]
  have hQ : ∀ h : ↥(PhiDeg M M' d hMM' hdd), (h : SL(2, ℤ)) ∈ Gamma 4 →
      ((h : SL(2, ℤ)) ∈ ModularCurve.PDPairing.Gamma0Upper (4 * d) ↔
        (((eDeg M M' d hMM' hdd).symm h : ↥(Gamma0 M')) : SL(2, ℤ)) ∈ Gamma 4) := by
    intro h hh4
    obtain ⟨g, rfl⟩ : ∃ g, eDeg M M' d hMM' hdd g = h := ⟨(eDeg M M' d hMM' hdd).symm h, MulEquiv.apply_symm_apply _ _⟩
    rw [MulEquiv.symm_apply_apply]
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
    rw [coe_eDeg, Gamma_mem, e00, e01, e10, e11] at hh4
    obtain ⟨h00, h01, h10, h11⟩ := hh4
    rw [coe_eDeg, ModularCurve.PDPairing.mem_Gamma0Upper, Gamma_mem, e01, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h4d : ((4 * d : ℕ) : ℤ) = 4 * (d : ℤ) := by push_cast; ring
    have hc4 : (((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
      rw [Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)] at h10
      exact dvd_trans (dvd_mul_left _ _) h10
    rw [h4d]
    constructor
    · intro hb
      refine ⟨h00, ?_, hc4, h11⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (mul_dvd_mul_iff_right hd0).mp hb
    · rintro ⟨-, hb, -, -⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb
      exact mul_dvd_mul hb (dvd_refl _)
  have hdet : 0 < (!![(d : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]
    simp only [mul_one, mul_zero, sub_zero]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [jDeg0_eq, iDeg0_eq]
  exact pairD_cores_transport (Γ' := Gamma0 M') (Γ'' := Gamma0 M) (Φ'' := PhiDeg M M' d hMM' hdd)
    (P := Gamma0 (4 * d)) (Q := ModularCurve.PDPairing.Gamma0Upper (4 * d)) (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd)
    !![(d : ℤ), 0; 0, 1] hdet (eDeg_intertwine M M' d hMM' hdd) hP hQ x' y hx' hy

section InstPD2

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [NeZero N] [NeZero ℓ] in
theorem Gamma0_mul_le : Gamma0 (N * ℓ) ≤ Gamma0 N := by
  intro g hg
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
  exact dvd_trans (by push_cast; exact Dvd.intro _ rfl) hg

omit [NeZero ℓ] in
theorem mul_div_eq : N * ℓ / N = ℓ := Nat.mul_div_cancel_left ℓ (Nat.pos_of_ne_zero (NeZero.ne N))

omit [NeZero ℓ] in
theorem dvd_mul_div : ℓ ∣ N * ℓ / N := by rw [mul_div_eq]

omit [NeZero N] [NeZero ℓ] in

theorem iDeg0_one_eq_res (φ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ = res (Gamma0_mul_le N ℓ) φ := by
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Gamma0 (N * ℓ)), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g)) =
    φ (Additive.ofMul (Subgroup.inclusion (Gamma0_mul_le N ℓ) g))
  have : ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g = Subgroup.inclusion (Gamma0_mul_le N ℓ) g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g
    fin_cases i <;> fin_cases j
    · simpa using e00
    · simpa using e01
    · simpa using e10
    · simpa using e11
  rw [this]

theorem heckeT0_eq_jDeg0 (φ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.heckeT0 N ℓ R φ =
      ModularCurve.PDPairing.jDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) (res (Gamma0_mul_le N ℓ) φ) := by

  have hmemNℓ : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb ∈ Gamma0 (N * ℓ) := by
    intro h hb
    rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hN : (N : ℤ) ∣ (h : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.2)
    push_cast
    exact mul_dvd_mul hN (dvd_refl _)
  have hιU : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        ⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩ = h := by
    intro h hb
    apply Subtype.ext
    exact ModularCurve.PDPairing.conjLowerMat_conjUpperMat ℓ (h : SL(2, ℤ)) hb
      (by rw [ModularCurve.PDPairing.conjUpperMat_apply_10]; exact dvd_mul_left _ _)
  have hK : ModularCurve.PDPairing.Gamma0HUpper N ℓ = (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)).range := by
    ext h
    constructor
    · intro hh
      have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, hh⟩
      exact ⟨_, hιU h hb⟩
    · rintro ⟨g, rfl⟩
      show ((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈
        ModularCurve.PDPairing.Gamma0Upper ℓ
      rw [ModularCurve.PDPairing.mem_Gamma0Upper, (iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g).2.1,
        Int.cast_mul]
      simp
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (ModularCurve.PDPairing.conjL0 N ℓ))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) ℓ R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) (res (Gamma0_mul_le N ℓ) φ))))
  congr 1
  refine transfer_eq_of_eq hK _ _ (fun h h₁ h₂ => ?_)
  show Multiplicative.ofAdd (φ (Additive.ofMul (ModularCurve.PDPairing.conjL0 N ℓ ⟨h, h₁⟩))) =
    Multiplicative.ofAdd (φ (Additive.ofMul (Subgroup.inclusion (Gamma0_mul_le N ℓ)
      ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ))).symm
        ⟨h, h₂⟩))))
  congr 3
  have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, h₁⟩
  have hg₀ : (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ)
      (dvd_mul_div N ℓ))).symm ⟨h, h₂⟩ = ⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩ := by
    apply ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
    apply Subtype.ext
    rw [MonoidHom.apply_ofInjective_symm, hιU h hb]
  rw [hg₀]
  rfl

theorem transfer_comp_equiv_rel {G G' A : Type*} [Group G] [Group G'] [CommGroup A] (σ : G ≃* G')
    (L : Subgroup G) (L' : Subgroup G') [L.FiniteIndex] [L'.FiniteIndex] (hL : ∀ g, g ∈ L ↔ σ g ∈ L')
    (χ : L →* A) (χ' : L' →* A) (hχ : ∀ (g : G) (h : g ∈ L) (h' : σ g ∈ L'), χ ⟨g, h⟩ = χ' ⟨σ g, h'⟩) :
    (MonoidHom.transfer χ').comp σ.toMonoidHom = MonoidHom.transfer χ := by
  have hK : L'.comap σ.toMonoidHom = L := by
    ext g
    rw [Subgroup.mem_comap]
    exact (hL g).symm
  ext g
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ModularCurve.PDPairing.T1.transfer_congr σ L' χ' g]
  revert g
  rw [← MonoidHom.ext_iff]
  exact transfer_eq_of_eq hK _ _ (fun g h₁ h₂ => (hχ g h₂ h₁).symm)

theorem comp_conj_eq {G A : Type*} [Group G] [CommGroup A] (f : G →* A) (γ : G) :
    f.comp (MulAut.conj γ).toMonoidHom = f := by
  ext g
  show f (γ * g * γ⁻¹) = f g
  rw [map_mul, map_mul, map_inv, mul_comm (f γ) (f g), mul_assoc, mul_inv_cancel, mul_one]

omit [NeZero N] [NeZero ℓ] in
theorem iotaDeg0_one_eq (g : ↥(Gamma0 (N * ℓ))) :
    ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g = Subgroup.inclusion (Gamma0_mul_le N ℓ) g := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

theorem D_mul_iotaDeg0 (k : ↥(Gamma0 (N * ℓ))) :
    !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k :
        ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] := by
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k
  have hc : (ℓ : ℤ) * ((k : SL(2, ℤ)) 1 0 / ℓ) = (k : SL(2, ℤ)) 1 0 :=
    Int.mul_ediv_cancel' (ModularCurve.PDPairing.dvd_entry0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, hc, mul_comm]

omit [NeZero ℓ] in

theorem conjUpperMat_mul_D (h : SL(2, ℤ)) (hb : (ℓ : ℤ) ∣ h 0 1) :
    ((ModularCurve.PDPairing.conjUpperMat ℓ h hb : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] =
      !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hb' : (h : SL(2, ℤ)) 0 1 / ℓ * ℓ = (h : SL(2, ℤ)) 0 1 := Int.ediv_mul_cancel hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hb', mul_comm]

omit [NeZero ℓ] in

theorem entries_of_intertwine (X Y : Matrix (Fin 2) (Fin 2) ℤ)
    (h : X * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * Y) :
    Y 0 1 = X 0 1 * ℓ ∧ X 1 0 = ℓ * Y 1 0 := by
  have e := fun i j => congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M i j) h
  have e01 := e 0 1
  have e10 := e 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  exact ⟨e01.symm, e10⟩

theorem coset_transport (γ₁ γ₂ g₀ g : SL(2, ℤ))
    (hcoset : (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
    (h : !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (g₀ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) :
    ((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] =
      !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hDD' : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = (ℓ : ℤ) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hD'smul : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M * ((ℓ : ℤ) • 1) = ((ℓ : ℤ) • 1) * M := by
    intro M; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hdetD : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]

  have e1 : (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
    apply cancel_det hdetD
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hDD', ← Matrix.mul_assoc, hDD', hD'smul]

  have hx : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1; group
  have hy : ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1; group
  have hdet1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
  have hdet2 : (γ₂ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
  apply cancel_det hdet1
  apply cancel_det_right hdet2
  calc (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) *
        (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
      = (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] *
          (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [← Matrix.mul_assoc, hx]; simp only [Matrix.mul_assoc]
    _ = (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by rw [← hcoset]
    _ = !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := e1
    _ = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) *
          (g : Matrix (Fin 2) (Fin 2) ℤ) := by rw [← hcoset]
    _ = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] *
          ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
          simp only [Matrix.mul_assoc, hy]

theorem Gamma0HUpper_eq_range :
    ModularCurve.PDPairing.Gamma0HUpper N ℓ = (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)).range := by
  have hmemNℓ : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb ∈ Gamma0 (N * ℓ) := by
    intro h hb
    rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hN : (N : ℤ) ∣ (h : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.2)
    push_cast
    exact mul_dvd_mul hN (dvd_refl _)
  ext h
  constructor
  · intro hh
    have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, hh⟩
    refine ⟨⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩, Subtype.ext ?_⟩
    exact ModularCurve.PDPairing.conjLowerMat_conjUpperMat ℓ (h : SL(2, ℤ)) hb
      (by rw [ModularCurve.PDPairing.conjUpperMat_apply_10]; exact dvd_mul_left _ _)
  · rintro ⟨g, rfl⟩
    show ((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈
      ModularCurve.PDPairing.Gamma0Upper ℓ
    rw [ModularCurve.PDPairing.mem_Gamma0Upper, (iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g).2.1,
      Int.cast_mul]
    simp

omit [NeZero N] [NeZero ℓ] in

theorem mem_range_iotaDeg0_one (g : ↥(Gamma0 N)) :
    g ∈ (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)).range ↔ (g : SL(2, ℤ)) ∈ Gamma0 (N * ℓ) := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [iotaDeg0_one_eq]
    exact k.2
  · intro hg
    exact ⟨⟨g, hg⟩, by rw [iotaDeg0_one_eq]; rfl⟩

theorem jDeg0_iDeg0_symm (hℓN : Nat.Coprime ℓ N) (ψ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.jDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) ψ) =
      ModularCurve.PDPairing.jDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hcoset⟩ := hecke_coset_symm N ℓ hℓN
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩

  have hdetD : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]
  let ιℓ := ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
  let ι₁ := ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)
  let σ : ↥(Gamma0 N) ≃* ↥(Gamma0 N) := MulAut.conj (⟨γ₂, hγ₂⟩ : ↥(Gamma0 N))
  have hσ : ∀ g : ↥(Gamma0 N), ((σ g : ↥(Gamma0 N)) : SL(2, ℤ)) = γ₂ * g * γ₂⁻¹ := fun g => rfl

  have hA : ∀ g : ↥(Gamma0 N), g ∈ ι₁.range ↔ σ g ∈ ιℓ.range := by
    intro g
    rw [mem_range_iotaDeg0_one, ← Gamma0HUpper_eq_range]
    constructor
    · intro hg

      have h1 := coset_transport ℓ γ₁ γ₂ _ _ hcoset (D_mul_iotaDeg0 N ℓ ⟨g, hg⟩)
      show ((σ g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ ModularCurve.PDPairing.Gamma0Upper ℓ
      rw [ModularCurve.PDPairing.mem_Gamma0Upper, hσ, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e01 := (entries_of_intertwine ℓ _ _ h1).1
      exact ⟨_, by rw [e01, mul_comm]⟩
    · intro hh
      have hb : (ℓ : ℤ) ∣ ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ))) 0 1 := by
        have := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨σ g, hh⟩
        rwa [hσ] at this

      have h3 := conjUpperMat_mul_D ℓ (γ₂ * g * γ₂⁻¹) hb

      have hDD' : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = (ℓ : ℤ) • 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hdet1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
        rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
      have hdetD' : (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]
      set g' : SL(2, ℤ) := ModularCurve.PDPairing.conjUpperMat ℓ (γ₂ * g * γ₂⁻¹) hb with hg'
      have h4 : !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] := by
        apply cancel_det_right hdet1
        apply cancel_det_right hdetD
        apply cancel_det_right (a := (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
          (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero)
        have hx : ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) =
            (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (g' : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]; congr 1; group
        have hy : ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) =
            (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]; congr 1; group
        calc !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
              (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
            = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((g' : Matrix (Fin 2) (Fin 2) ℤ) *
                !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
                rw [Matrix.mul_assoc (!![(1 : ℤ), 0; 0, (ℓ : ℤ)]), hx]; simp only [Matrix.mul_assoc]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] *
                ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h3]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] *
                (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
                simp only [Matrix.mul_assoc, hy]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := by rw [← hcoset]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1]) := by
                rw [hDD', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
                !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) := by rw [← hcoset, Matrix.mul_assoc]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
                !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by simp only [Matrix.mul_assoc]

      have hmem : (γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) ∈ Gamma0 N := by
        refine (Gamma0 N).mul_mem ((Gamma0 N).mul_mem hγ₁ ?_) ((Gamma0 N).inv_mem hγ₁)
        have : ModularCurve.PDPairing.conjUpperMat ℓ (γ₂ * g * γ₂⁻¹) hb ∈ Gamma0 (N * ℓ) := by
          rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
          have hN : (N : ℤ) ∣ ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ))) 1 0 := by
            have := Gamma0_mem.mp (σ g).2
            rw [hσ] at this
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
          push_cast
          exact mul_dvd_mul hN (dvd_refl _)
        exact Gamma0_mul_le N ℓ this
      have e10 := (entries_of_intertwine ℓ _ _ h4.symm).2
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hN' : (N : ℤ) ∣ ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ))) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hmem)
      rw [e10]
      push_cast
      rw [mul_comm (N : ℤ) (ℓ : ℤ)]
      exact mul_dvd_mul (dvd_refl _) hN'

  show MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) ℓ R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) ψ)))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) 1 R (dvd_mul_right N ℓ) (one_dvd _)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ))))
  congr 1

  rw [← transfer_comp_equiv_rel σ ι₁.range ιℓ.range hA _ _ ?hχ, comp_conj_eq]
  case hχ =>
    intro g h₁ hℓ'

    show Multiplicative.ofAdd (ψ (Additive.ofMul (ιℓ ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _))).symm ⟨g, h₁⟩)))) =
      Multiplicative.ofAdd (ψ (Additive.ofMul (ι₁ ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ))).symm ⟨σ g, hℓ'⟩))))
    congr 1
    set k := (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _))).symm
      ⟨g, h₁⟩ with hk
    set k' := (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ)
      (dvd_mul_div N ℓ))).symm ⟨σ g, hℓ'⟩ with hk'
    have hkg : ((k : ↥(Gamma0 (N * ℓ))) : SL(2, ℤ)) = (g : SL(2, ℤ)) := by
      have e := MonoidHom.apply_ofInjective_symm
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)) ⟨g, h₁⟩
      rw [← hk, iotaDeg0_one_eq] at e
      exact congrArg (fun x : ↥(Gamma0 N) => (x : SL(2, ℤ))) e
    have hk'σ : ιℓ k' = σ g := by
      have e := MonoidHom.apply_ofInjective_symm
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)) ⟨σ g, hℓ'⟩
      rw [← hk'] at e
      exact e

    have hF1 := D_mul_iotaDeg0 N ℓ k
    rw [hkg] at hF1
    have hT := coset_transport ℓ γ₁ γ₂ _ _ hcoset hF1
    have hF1' := D_mul_iotaDeg0 N ℓ k'
    have hk'mat : (((ιℓ k' : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hk'σ, hσ]
    rw [hk'mat] at hF1'

    have hkk : ((k' : ↥(Gamma0 (N * ℓ))) : SL(2, ℤ)) = γ₁⁻¹ * ((ιℓ k : ↥(Gamma0 N)) : SL(2, ℤ)) * γ₁ := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      have := cancel_det_right hdetD (hF1'.symm.trans hT.symm)
      rw [this]

    have : ι₁ k' = (⟨γ₁, hγ₁⟩ : ↥(Gamma0 N))⁻¹ * ιℓ k * ⟨γ₁, hγ₁⟩ := by
      apply Subtype.ext
      rw [iotaDeg0_one_eq]
      exact hkk
    rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel

end InstPD2
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem pairD_hecke_selfAdjoint [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ ψ : Additive ↥(Gamma0 N) →+ R) (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN
  have hpar1 : ∀ χ : Additive ↥(Gamma0 N) →+ R, IsParabolicHom (Gamma0 N) χ →
      IsParabolicHom (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) χ) :=
    fun χ hχ => ModularCurve.PDPairing.iDeg0_mem_parabolicHoms R N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) χ hχ
  have hparℓ : ∀ χ : Additive ↥(Gamma0 N) →+ R, IsParabolicHom (Gamma0 N) χ →
      IsParabolicHom (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) χ) :=
    fun χ hχ => ModularCurve.PDPairing.iDeg0_mem_parabolicHoms R N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) χ hχ
  have hL : pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
    rw [heckeT0_eq_jDeg0 N ℓ φ, ← iDeg0_one_eq_res N ℓ φ,
      pairD_jDeg0_iDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) _ ψ (hpar1 φ hφ) hψ]
  have hR : pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) =
      pairD (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
    rw [heckeT0_eq_jDeg0 N ℓ ψ, ← iDeg0_one_eq_res N ℓ ψ, jDeg0_iDeg0_symm N ℓ hcop ψ,
      pairD_swap (Gamma 4) (Gamma0 N)
        (ModularCurve.PDPairing.jDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _)
          (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ)) φ,
      pairD_jDeg0_iDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) _ φ (hparℓ ψ hψ) hφ,
      pairD_swap (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ), neg_neg]
  exact hL.trans hR.symm

theorem isPar_iff_isParabolicHom (Γ' : Subgroup SL(2, ℤ)) (φ : Additive Γ' →+ R) :
    IsPar Γ' φ ↔ IsParabolicHom Γ' φ := Iff.rfl

end Inst
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section JointInhabitants

p2m_open "CongruenceSubgroup P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

noncomputable scoped instance isFreeGroup_Gamma_four : IsFreeGroup ↥(Gamma 4) :=
  IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe gamma_four_le_sanov)

noncomputable scoped instance invertibleTwoRat : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
noncomputable scoped instance invertibleSixRat : Invertible (6 : ℚ) := invertibleOfNonzero (by norm_num)

theorem isParabolicHom_zero (Γ : Subgroup SL(2, ℤ)) : IsParabolicHom Γ (0 : Additive Γ →+ ℚ) :=
  fun _ _ => rfl

theorem jointInhabitant_PD2 :
    pairD (Gamma 4) (Gamma0 11) (ModularCurve.PDPairing.heckeT0 11 2 ℚ 0) 0 = pairD (Gamma 4) (Gamma0 11) 0 (ModularCurve.PDPairing.heckeT0 11 2 ℚ 0) :=
  pairD_hecke_selfAdjoint (R := ℚ) 11 2 Nat.prime_two (by norm_num) 0 0 (isParabolicHom_zero _) (isParabolicHom_zero _)

theorem jointInhabitant_PD3 :
    pairD (Gamma 4) (Gamma0 11) (ModularCurve.PDPairing.jDeg0 11 22 2 ℚ ℚ (by norm_num) (by norm_num) 0) 0 =
      pairD (Gamma 4) (Gamma0 22) 0 (ModularCurve.PDPairing.iDeg0 11 22 2 ℚ ℚ (by norm_num) (by norm_num) 0) :=
  pairD_jDeg0_iDeg0 (R := ℚ) 11 22 2 (by norm_num) (by norm_num) 0 0 (isParabolicHom_zero _) (isParabolicHom_zero _)

end JointInhabitants
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section ShapeDiff

p2m_open "CongruenceSubgroup P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [Invertible (6 : R)]

theorem neZero_left_of_mul (N q' : ℕ) [h : NeZero (N * q')] : NeZero N :=
  ⟨fun hN => h.out (by rw [hN, zero_mul])⟩

theorem dvd_mul_div_left (N q' : ℕ) [NeZero N] : q' ∣ N * q' / N :=
  ⟨1, by rw [Nat.mul_div_cancel_left q' (Nat.pos_of_ne_zero (NeZero.ne N)), mul_one]⟩

theorem P2_of_PD2_upper (N q' ℓ : ℕ) [NeZero (N * q')] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNq : ¬ ℓ ∣ N * q')
    (φ ψ : Additive ↥(Gamma0 (N * q')) →+ R)
    (hφ : IsParabolicHom (Gamma0 (N * q')) φ) (hψ : IsParabolicHom (Gamma0 (N * q')) ψ) :
    pairD (Gamma 4) (Gamma0 (N * q')) (ModularCurve.PDPairing.heckeT0 (N * q') ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 (N * q')) φ (ModularCurve.PDPairing.heckeT0 (N * q') ℓ R ψ) :=
  pairD_hecke_selfAdjoint (N * q') ℓ hℓ hℓNq φ ψ hφ hψ

theorem P2_of_PD2_lower (N q' ℓ : ℕ) [NeZero (N * q')] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNq : ¬ ℓ ∣ N * q')
    (φ ψ : Additive ↥(Gamma0 N) →+ R)
    (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_hecke_selfAdjoint N ℓ hℓ (fun h => hℓNq (dvd_mul_of_dvd_left h q')) φ ψ hφ hψ

theorem P3_of_PD3_iota0 (N q' : ℕ) [NeZero (N * q')] [NeZero q']
    (x' : Additive ↥(Gamma0 (N * q')) →+ R) (y : Additive ↥(Gamma0 N) →+ R)
    (hx' : IsParabolicHom (Gamma0 (N * q')) x') (hy : IsParabolicHom (Gamma0 N) y) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.jDeg0 N (N * q') 1 R R (dvd_mul_right N q') (one_dvd _) x') y =
      pairD (Gamma 4) (Gamma0 (N * q')) x'
        (ModularCurve.PDPairing.iDeg0 N (N * q') 1 R R (dvd_mul_right N q') (one_dvd _) y) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_jDeg0_iDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _) x' y hx' hy

theorem P3_of_PD3_iota1 (N q' : ℕ) [NeZero (N * q')] [NeZero q']
    (x' : Additive ↥(Gamma0 (N * q')) →+ R) (y : Additive ↥(Gamma0 N) →+ R)
    (hx' : IsParabolicHom (Gamma0 (N * q')) x') (hy : IsParabolicHom (Gamma0 N) y) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N)
        (ModularCurve.PDPairing.jDeg0 N (N * q') q' R R (dvd_mul_right N q') (dvd_mul_div_left N q') x') y =
      pairD (Gamma 4) (Gamma0 (N * q')) x'
        (ModularCurve.PDPairing.iDeg0 N (N * q') q' R R (dvd_mul_right N q') (dvd_mul_div_left N q') y) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_jDeg0_iDeg0 N (N * q') q' (dvd_mul_right N q') (dvd_mul_div_left N q') x' y hx' hy

end ShapeDiff
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section DefPDInhabitants

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

noncomputable example :
    parabolicHoms ℤ (Gamma0 11) ℤ →ₗ[ℤ] parabolicHoms ℤ (Gamma0 11) ℤ →ₗ[ℤ] ℤ :=
  ModularCurve.PDPairing.pairZ 11

theorem defpd_inhabitant_pairZ :
    ModularCurve.PDPairing.pairZ 11 ⟨0, Submodule.zero_mem _⟩ ⟨0, Submodule.zero_mem _⟩ =
      ModularCurve.PDPairing.pairZFun 11 0 0 := rfl

theorem defpd_inhabitant_pairZFun : ∃ z : ℤ, ModularCurve.PDPairing.pairZFun 11 0 0 = z := ⟨_, rfl⟩

theorem defpd_inhabitant_pairD :
    ∃ r : ℚ, ModularCurve.PDPairing.pairD (Gamma 4) (Gamma0 11) (0 : Additive ↥(Gamma0 11) →+ ℚ) 0 = r :=
  ⟨_, rfl⟩

theorem defpd_inhabitant_pairF :
    ∃ r : ℚ, ModularCurve.PDPairing.pairF (Gamma 4) (0 : Additive ↥(Gamma 4) →+ ℚ) 0 = r := ⟨_, rfl⟩

noncomputable example : (Additive ↥(Gamma0 11) →+ ℤ) →+ (Additive ↥(Gamma0 11) →+ ℤ) :=
  ModularCurve.PDPairing.heckeT0 11 2 ℤ

noncomputable example : (Additive ↥(Gamma0 11) →+ ℤ) →ₗ[ℤ] (Additive ↥(Gamma0 22) →+ ℤ) :=
  ModularCurve.PDPairing.iDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num)

noncomputable example : (Additive ↥(Gamma0 22) →+ ℤ) →ₗ[ℤ] (Additive ↥(Gamma0 11) →+ ℤ) :=
  ModularCurve.PDPairing.jDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num)

theorem defpd_inhabitant_heckeT0 : ModularCurve.PDPairing.heckeT0 11 2 ℤ 0 = 0 := map_zero _
theorem defpd_inhabitant_iDeg0 :
    ModularCurve.PDPairing.iDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num) 0 = 0 := map_zero _
theorem defpd_inhabitant_jDeg0 :
    ModularCurve.PDPairing.jDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num) 0 = 0 := map_zero _

example : Module ℤ ↥(parabolicHoms ℤ (Gamma0 11) ℤ) := inferInstance
example : AddCommGroup ↥(parabolicHoms ℤ (Gamma0 11) ℤ) := inferInstance

end DefPDInhabitants
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section CastLayer

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

variable {R : Type*} [CommRing R]

def castChar {G : Type*} [MulOneClass G] {A B : Type*} [AddZeroClass A] [AddZeroClass B] (f : A →+ B)
    (φ : Additive G →+ A) : Additive G →+ B :=
  f.comp φ

@[scoped simp] theorem castChar_apply {G : Type*} [MulOneClass G] {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    (f : A →+ B) (φ : Additive G →+ A) (x : Additive G) : castChar f φ x = f (φ x) := rfl

section PrimCast

variable {Φ : Type*} [Group Φ] {S : Type*} [CommRing S]

theorem omega_castChar (f : R →+* S) (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (castChar f.toAddMonoidHom φ) (castChar f.toAddMonoidHom ψ) g g' = f (omega φ ψ g g') := by
  simp only [omega, castChar_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_sub, map_mul]

variable [IsFreeGroup Φ]

theorem hPrim_castChar (f : R →+* S) (φ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (castChar f.toAddMonoidHom φ) (castChar f.toAddMonoidHom ψ) g = f (hPrim φ ψ g) := by
  symm
  refine hPrim_unique _ _ (fun g => f (hPrim φ ψ g)) ?_ ?_ g
  · intro g g'
    rw [hPrim_mul, omega_castChar, map_sub, map_add]
  · intro a
    rw [hPrim_of, map_zero]

end PrimCast
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem cuspSum_map (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {S : Type*} [CommRing S] (f : R →+* S) (h : Φ → R) :
    cuspSum Φ (fun g => f (h g)) = f (cuspSum Φ h) := by
  unfold cuspSum
  rw [map_sum]

theorem isParabolicHom_castChar {Γ : Subgroup SL(2, ℤ)} {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) {φ : Additive Γ →+ A} (hφ : IsParabolicHom Γ φ) : IsParabolicHom Γ (castChar f φ) :=
  fun γ hγ => by rw [castChar_apply, hφ γ hγ, map_zero]

theorem coresAdd_castChar {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥K →+ A) :
    ModularCurve.PDPairing.coresAdd K (castChar f φ) = castChar f (ModularCurve.PDPairing.coresAdd K φ) := by
  ext g
  simp only [ModularCurve.PDPairing.coresAdd, MonoidHom.toAdditiveLeft_apply_apply, castChar_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem heckeT0_castChar (M ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (φ : Additive ↥(Gamma0 M) →+ A) :
    ModularCurve.PDPairing.heckeT0 M ℓ B (castChar f φ) = castChar f (ModularCurve.PDPairing.heckeT0 M ℓ A φ) := by
  ext g
  simp only [ModularCurve.PDPairing.heckeT0_apply, MonoidHom.toAdditiveLeft_apply_apply, castChar_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem iDeg0_castChar (M M' d : ℕ) [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+ B) (φ : Additive ↥(Gamma0 M) →+ A) :
    ModularCurve.PDPairing.iDeg0 M M' d B B hMM' hdd (castChar f φ) =
      castChar f (ModularCurve.PDPairing.iDeg0 M M' d A A hMM' hdd φ) := by
  ext; rfl

theorem jDeg0_castChar (M M' d : ℕ) [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) {A B : Type*}
    [CommRing A] [CommRing B] (f : A →+ B) (φ : Additive ↥(Gamma0 M') →+ A) :
    ModularCurve.PDPairing.jDeg0 M M' d B B hMM' hdd (castChar f φ) =
      castChar f (ModularCurve.PDPairing.jDeg0 M M' d A A hMM' hdd φ) := by
  show ModularCurve.PDPairing.coresAdd _ (ModularCurve.PDPairing.pushChar0 M M' d B hMM' hdd (castChar f φ)) =
    castChar f (ModularCurve.PDPairing.coresAdd _ (ModularCurve.PDPairing.pushChar0 M M' d A hMM' hdd φ))
  rw [← coresAdd_castChar]
  rfl

abbrev ratChar {G : Type*} [MulOneClass G] (φ : Additive G →+ ℤ) : Additive G →+ ℚ :=
  castChar (Int.castRingHom ℚ).toAddMonoidHom φ

theorem pairZFun_cast [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    ((ModularCurve.PDPairing.pairZFun N φ ψ : ℤ) : ℚ) =
      96 * pairD (Gamma 4) (Gamma0 N) (ratChar φ) (ratChar ψ) := by
  have hn : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ∣ 48 := index_Gamma_four ▸ relIndex_inf_Gamma4_dvd (Gamma0 N)
  have hn0 : (((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : ℚ) ≠ 0 := by
    have : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ≠ 0 := fun h => by rw [h] at hn; exact absurd hn (by decide)
    exact_mod_cast this
  have hres : ∀ χ : Additive ↥(Gamma0 N) →+ ℤ,
      resInf (Gamma 4) (Gamma0 N) (ratChar χ) = castChar (Int.castRingHom ℚ).toAddMonoidHom (resInf (Gamma 4) (Gamma0 N) χ) :=
    fun χ => rfl
  have hprim : hPrim (resInf (Gamma 4) (Gamma0 N) (ratChar φ)) (resInf (Gamma 4) (Gamma0 N) (ratChar ψ)) =
      fun g => (Int.castRingHom ℚ) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) g) := by
    funext g
    rw [hres, hres, hPrim_castChar]
  unfold ModularCurve.PDPairing.pairZFun pairD pairF
  rw [hprim, cuspSum_map, invOf_eq_inv, invOf_eq_inv, Int.cast_mul, Int.cast_natCast, Nat.cast_div hn hn0]
  simp only [eq_intCast, Nat.cast_ofNat]
  field_simp
  ring

theorem pairZFun_heckeT0_comm [IsFreeGroup ↥(Gamma 4)] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) (hφ : IsParabolicHom (Gamma0 N) φ)
    (hψ : IsParabolicHom (Gamma0 N) ψ) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.heckeT0 N ℓ ℤ φ) ψ =
      ModularCurve.PDPairing.pairZFun N φ (ModularCurve.PDPairing.heckeT0 N ℓ ℤ ψ) := by
  apply Int.cast_injective (α := ℚ)
  rw [pairZFun_cast, pairZFun_cast]
  unfold ratChar
  rw [← heckeT0_castChar, ← heckeT0_castChar]
  congr 1
  exact pairD_hecke_selfAdjoint N ℓ hℓ hℓN _ _ (isParabolicHom_castChar _ hφ) (isParabolicHom_castChar _ hψ)

theorem pairZFun_jDeg0_iDeg0 [IsFreeGroup ↥(Gamma 4)] (N N' d : ℕ) [NeZero N] [NeZero N'] [NeZero d]
    (hNN' : N ∣ N') (hdd : d ∣ N' / N) (x' : Additive ↥(Gamma0 N') →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ)
    (hx' : IsParabolicHom (Gamma0 N') x') (hy : IsParabolicHom (Gamma0 N) y) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.jDeg0 N N' d ℤ ℤ hNN' hdd x') y =
      ModularCurve.PDPairing.pairZFun N' x' (ModularCurve.PDPairing.iDeg0 N N' d ℤ ℤ hNN' hdd y) := by
  apply Int.cast_injective (α := ℚ)
  rw [pairZFun_cast, pairZFun_cast]
  unfold ratChar
  rw [← jDeg0_castChar, ← iDeg0_castChar]
  congr 1
  exact pairD_jDeg0_iDeg0 N N' d hNN' hdd _ _ (isParabolicHom_castChar _ hx') (isParabolicHom_castChar _ hy)

end CastLayer
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section B12

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

def sixInt : Subring ℚ where
  carrier := {q | ∃ (k : ℕ) (m : ℤ), q = m / 6 ^ k}
  mul_mem' := by
    rintro a b ⟨k, m, rfl⟩ ⟨k', m', rfl⟩
    refine ⟨k + k', m * m', ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  one_mem' := ⟨0, 1, by norm_num⟩
  add_mem' := by
    rintro a b ⟨k, m, rfl⟩ ⟨k', m', rfl⟩
    refine ⟨k + k', m * 6 ^ k' + m' * 6 ^ k, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  zero_mem' := ⟨0, 0, by norm_num⟩
  neg_mem' := by
    rintro a ⟨k, m, rfl⟩
    exact ⟨k, -m, by push_cast; ring⟩

theorem mem_sixInt_iff (q : ℚ) : q ∈ sixInt ↔ ∃ (k : ℕ) (m : ℤ), q = m / 6 ^ k := Iff.rfl

theorem intCast_mem_sixInt (m : ℤ) : (m : ℚ) ∈ sixInt := ⟨0, m, by norm_num⟩

def intToSix : ℤ →+* ↥sixInt := (Int.castRingHom ↥sixInt)

theorem coe_intToSix (m : ℤ) : ((intToSix m : ↥sixInt) : ℚ) = m := by
  simp [intToSix]

theorem coe_two_sixInt : ((2 : ↥sixInt) : ℚ) = 2 := map_ofNat sixInt.subtype 2
theorem coe_six_sixInt : ((6 : ↥sixInt) : ℚ) = 6 := map_ofNat sixInt.subtype 6

noncomputable scoped instance invertibleTwoSix : Invertible (2 : ↥sixInt) where
  invOf := ⟨1 / 2, 1, 3, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_two_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_two_sixInt]; norm_num)

noncomputable scoped instance invertibleSixSix : Invertible (6 : ↥sixInt) where
  invOf := ⟨1 / 6, 1, 1, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_six_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_six_sixInt]; norm_num)

theorem int_dvd_of_sixInt_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (x : ℤ) (a : ↥sixInt)
    (h : (x : ↥sixInt) = (p : ↥sixInt) * a) : (p : ℤ) ∣ x := by
  obtain ⟨k, m, hm⟩ := a.2
  have hq : (x : ℚ) = p * (m / 6 ^ k) := by
    have := congrArg (fun t : ↥sixInt => (t : ℚ)) h
    push_cast at this
    rw [this, ← hm]
  have hZ : x * 6 ^ k = p * m := by
    have h6 : (6 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp at hq
    exact_mod_cast hq
  have hp2 : ¬ (p ∣ 2) := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hp3 : ¬ (p ∣ 3) := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hcop6 : Nat.Coprime p 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
    exact ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hp2, (Nat.Prime.coprime_iff_not_dvd hp).mpr hp3⟩
  have hcop : IsCoprime (p : ℤ) ((6 : ℤ) ^ k) := by
    apply IsCoprime.pow_right
    exact_mod_cast (Nat.isCoprime_iff_coprime.mpr hcop6)
  have hdvd : (p : ℤ) ∣ x * 6 ^ k := ⟨m, by rw [hZ]⟩
  exact hcop.dvd_of_dvd_mul_right hdvd

scoped instance : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

example (N : ℕ) [NeZero N] : Group.FG ↥(Gamma0 N) := inferInstance

theorem exists_common_denominator {G : Type*} [Group G] [Group.FG G] (ψ : Additive G →+ ↥sixInt) :
    ∃ k : ℕ, ∀ g : G, ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ k = m := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)

  have hden : ∀ g : G, ∃ k : ℕ, ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ k = m := by
    intro g
    obtain ⟨k, m, hm⟩ := (ψ (Additive.ofMul g)).2
    exact ⟨k, m, by rw [hm]; field_simp⟩
  classical
  choose kf mf hmf using hden
  obtain ⟨s, rfl⟩ := hfin.exists_finset_coe
  refine ⟨s.sum kf, ?_⟩

  have key : ∀ g ∈ Subgroup.closure (s : Set G), ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ (s.sum kf) = m := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      have hle : kf x ≤ s.sum kf := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨mf x * 6 ^ d, ?_⟩
      rw [hd, pow_add, ← mul_assoc, hmf x]
      push_cast
      ring
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨mx, hx⟩ := ihx
      obtain ⟨my, hy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ofMul_mul, map_add, Subring.coe_add, add_mul, hx, hy]
      push_cast
      ring
    | inv x _ ihx =>
      obtain ⟨mx, hx⟩ := ihx
      refine ⟨-mx, ?_⟩
      rw [ofMul_inv, map_neg, Subring.coe_neg, neg_mul, hx]
      push_cast
      ring
  intro g
  exact key g (by rw [hS]; exact Subgroup.mem_top g)

theorem exists_common_denominator' {G : Type*} [Group G] [Group.FG G] (ψ : Additive G →+ ↥sixInt) :
    ∃ k : ℕ, ∀ g : G, ∃ m : ℤ, (6 : ↥sixInt) ^ k * ψ (Additive.ofMul g) = (m : ↥sixInt) := by
  obtain ⟨k, hk⟩ := exists_common_denominator ψ
  refine ⟨k, fun g => ?_⟩
  obtain ⟨m, hm⟩ := hk g
  refine ⟨m, Subtype.ext ?_⟩
  push_cast
  rw [coe_six_sixInt, mul_comm]
  exact_mod_cast hm

theorem coe_96_sixInt : ((96 : ↥sixInt) : ℚ) = 96 := map_ofNat sixInt.subtype 96

noncomputable scoped instance invertible96Six : Invertible (96 : ↥sixInt) where
  invOf := ⟨1 / 96, 5, 81, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_96_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_96_sixInt]; norm_num)

theorem natCast_ne_zero_sixInt (p : ℕ) (hp : p ≠ 0) : (p : ↥sixInt) ≠ 0 := by
  exact_mod_cast hp

section PairDLin

variable (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] {S : Type*} [CommRing S]
  [Invertible (2 : S)] [Invertible (6 : S)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : S)]

theorem pairD_add_left (φ₁ φ₂ ψ : Additive Γ →+ S) :
    pairD Λ Γ (φ₁ + φ₂) ψ = pairD Λ Γ φ₁ ψ + pairD Λ Γ φ₂ ψ := by
  unfold pairD
  rw [show resInf Λ Γ (φ₁ + φ₂) = resInf Λ Γ φ₁ + resInf Λ Γ φ₂ from rfl, pairF_add_left, mul_add]

theorem pairD_smul_left (r : S) (φ ψ : Additive Γ →+ S) : pairD Λ Γ (r • φ) ψ = r * pairD Λ Γ φ ψ := by
  unfold pairD
  rw [show resInf Λ Γ (r • φ) = r • resInf Λ Γ φ from rfl, pairF_smul_left]
  ring

theorem pairD_add_right (φ ψ₁ ψ₂ : Additive Γ →+ S) :
    pairD Λ Γ φ (ψ₁ + ψ₂) = pairD Λ Γ φ ψ₁ + pairD Λ Γ φ ψ₂ := by
  rw [pairD_swap, pairD_add_left, neg_add, ← pairD_swap, ← pairD_swap]

theorem pairD_smul_right (r : S) (φ ψ : Additive Γ →+ S) : pairD Λ Γ φ (r • ψ) = r * pairD Λ Γ φ ψ := by
  rw [pairD_swap, pairD_smul_left, pairD_swap]
  ring

noncomputable def pairDRight (φ : Additive Γ →+ S) : ↥(parSub Γ S) →ₗ[S] S where
  toFun ψ := pairD Λ Γ φ (ψ : Additive Γ →+ S)
  map_add' ψ₁ ψ₂ := by
    show pairD Λ Γ φ ((ψ₁ : Additive Γ →+ S) + ψ₂) = _
    rw [pairD_add_right]
  map_smul' r ψ := by
    show pairD Λ Γ φ (r • (ψ : Additive Γ →+ S)) = _
    rw [pairD_smul_right, smul_eq_mul]
    rfl

@[scoped simp] theorem pairDRight_apply (φ : Additive Γ →+ S) (ψ : ↥(parSub Γ S)) :
    pairDRight Λ Γ φ ψ = pairD Λ Γ φ (ψ : Additive Γ →+ S) := rfl

end PairDLin
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

theorem pairZFun_castR [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] {S : Type*} [CommRing S] [Invertible (2 : S)]
    [Invertible (6 : S)] (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    ((ModularCurve.PDPairing.pairZFun N φ ψ : ℤ) : S) =
      96 * pairD (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom φ)
        (castChar (Int.castRingHom S).toAddMonoidHom ψ) := by
  have hn : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ∣ 48 := index_Gamma_four ▸ relIndex_inf_Gamma4_dvd (Gamma0 N)
  have h1 : ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * ((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) =
      48 := by rw [← Nat.cast_mul, Nat.div_mul_cancel hn, Nat.cast_ofNat]
  have hA : ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) =
      48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) := by
    calc ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S)
        = ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) *
            ((((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S)) := by
          rw [mul_invOf_self, mul_one]
      _ = 48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) := by rw [← mul_assoc, h1]
  have hB : (96 : S) * ⅟(2 : S) = 48 := by
    rw [show (96 : S) = 48 * 2 by norm_num, mul_assoc, mul_invOf_self, mul_one]
  have hres : ∀ χ : Additive ↥(Gamma0 N) →+ ℤ,
      resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom χ) =
        castChar (Int.castRingHom S).toAddMonoidHom (resInf (Gamma 4) (Gamma0 N) χ) :=
    fun χ => rfl
  have hprim : hPrim (resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom φ))
      (resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom ψ)) =
      fun g => (Int.castRingHom S) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) g) := by
    funext g
    rw [hres, hres, hPrim_castChar]
  unfold ModularCurve.PDPairing.pairZFun pairD pairF
  rw [hprim, cuspSum_map, Int.cast_mul, Int.cast_natCast, hA]
  simp only [eq_intCast]
  set c : S := ((cuspSum (Gamma0 N ⊓ Gamma 4) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ)) : ℤ) : S)
  calc 48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * c
      = (96 * ⅟(2 : S)) * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * c := by rw [hB]
    _ = 96 * (⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * (⅟(2 : S) * c)) := by ring

theorem isPar_castChar_of_mem {Γ' : Subgroup SL(2, ℤ)} {A : Type*} [CommRing A] (f : ℤ →+ A)
    (x : ↥(parabolicHoms ℤ Γ' ℤ)) : IsPar Γ' (castChar f (x : Additive Γ' →+ ℤ)) :=
  (isPar_iff_isParabolicHom Γ' _).mpr (isParabolicHom_castChar f ((mem_parabolicHoms_iff).mp x.2))

theorem exists_eq_smul_of_dvd_apply {Γ' : Subgroup SL(2, ℤ)} (p : ℤ) (hp : p ≠ 0) (x : ↥(parabolicHoms ℤ Γ' ℤ))
    (h : ∀ g : Γ', p ∣ (x : Additive Γ' →+ ℤ) (Additive.ofMul g)) :
    ∃ x' : ↥(parabolicHoms ℤ Γ' ℤ), x = p • x' := by
  classical
  choose c hc using h
  let y : Additive Γ' →+ ℤ :=
    { toFun := fun g => c (Additive.toMul g)
      map_zero' := by
        have h0 := hc 1
        rw [ofMul_one, map_zero] at h0
        have : c 1 = 0 := by
          rcases mul_eq_zero.mp h0.symm with h' | h'
          · exact absurd h' hp
          · exact h'
        simpa using this
      map_add' := by
        intro a b
        apply mul_left_cancel₀ hp
        have ha := hc (Additive.toMul a)
        have hb := hc (Additive.toMul b)
        have hab := hc (Additive.toMul (a + b))
        simp only [ofMul_toMul] at ha hb hab
        rw [mul_add, ← ha, ← hb, ← hab, map_add] }
  have hy : ∀ g : Γ', (x : Additive Γ' →+ ℤ) (Additive.ofMul g) = p * y (Additive.ofMul g) := fun g => hc g
  have hypar : IsParabolicHom Γ' y := by
    intro γ hγ
    have hx0 : (x : Additive Γ' →+ ℤ) (Additive.ofMul γ) = 0 := (mem_parabolicHoms_iff.mp x.2) γ hγ
    have := hy γ
    rw [hx0] at this
    rcases mul_eq_zero.mp this.symm with h' | h'
    · exact absurd h' hp
    · exact h'
  refine ⟨⟨y, mem_parabolicHoms_iff.mpr hypar⟩, Subtype.ext (AddMonoidHom.ext fun g => ?_)⟩
  rw [Submodule.coe_smul, AddMonoidHom.smul_apply, smul_eq_mul]
  exact hy (Additive.toMul g)

theorem P1_of_wall [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hwall : ∀ l' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt) →ₗ[↥sixInt] ↥sixInt,
      ∃! φ₀' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt), ∀ ψ' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt),
        pairF (Gamma0 N ⊓ Gamma 4) (φ₀' : Additive ↥(Gamma0 N ⊓ Gamma 4) →+ ↥sixInt)
          (ψ' : Additive ↥(Gamma0 N ⊓ Gamma 4) →+ ↥sixInt) = l' ψ') :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') := by
  classical
  haveI : (Gamma 4).Normal := Gamma_normal 4
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpA : (p : ↥sixInt) ≠ 0 := natCast_ne_zero_sixInt p hp.ne_zero

  have hperf := fun l => pairD_perfect (R := ↥sixInt) (Gamma 4) (Gamma0 N) neg_one_not_mem_Gamma_four hwall l
  set ι : ℤ →+ ↥sixInt := (Int.castRingHom ↥sixInt).toAddMonoidHom with hιdef

  have left : ∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
        ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x' := by
    intro x hx
    set xA : ↥(parSub (Gamma0 N) ↥sixInt) := ⟨castChar ι (x : Additive ↥(Gamma0 N) →+ ℤ), isPar_castChar_of_mem ι x⟩
      with hxAdef

    have hvals : ∀ z : ↥(parSub (Gamma0 N) ↥sixInt),
        ∃ a : ↥sixInt, 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z = p * a := by
      intro z
      obtain ⟨k, hk⟩ := exists_common_denominator' (G := ↥(Gamma0 N)) (z : Additive ↥(Gamma0 N) →+ ↥sixInt)
      choose m hm using hk

      let y : Additive ↥(Gamma0 N) →+ ℤ :=
        { toFun := fun g => m (Additive.toMul g)
          map_zero' := by
            have h0 := hm 1
            rw [ofMul_one, map_zero, mul_zero] at h0
            exact_mod_cast (by simpa using h0.symm : ((m 1 : ℤ) : ↥sixInt) = 0)
          map_add' := by
            intro a b
            have ha := hm (Additive.toMul a)
            have hb := hm (Additive.toMul b)
            have hab := hm (Additive.toMul (a + b))
            simp only [ofMul_toMul] at ha hb hab
            rw [map_add, mul_add, ha, hb] at hab
            rw [toMul_add]
            exact_mod_cast hab.symm }
      have hy : castChar ι y = (6 : ↥sixInt) ^ k • (z : Additive ↥(Gamma0 N) →+ ↥sixInt) := by
        refine AddMonoidHom.ext fun g => ?_
        rw [castChar_apply, AddMonoidHom.smul_apply, smul_eq_mul]
        show ι (m (Additive.toMul g)) = 6 ^ k * (z : Additive ↥(Gamma0 N) →+ ↥sixInt) g
        have := hm (Additive.toMul g)
        simp only [ofMul_toMul] at this
        rw [this, hιdef]
        simp
      have hypar : IsParabolicHom (Gamma0 N) y := by
        intro γ hγ
        have hz : (z : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul γ) = 0 :=
          (show IsPar (Gamma0 N) (z : Additive ↥(Gamma0 N) →+ ↥sixInt) from z.2) γ hγ
        have := hm γ
        rw [hz, mul_zero] at this
        exact_mod_cast (show ((m γ : ℤ) : ↥sixInt) = 0 from this.symm)

      obtain ⟨c, hc⟩ := hx ⟨y, mem_parabolicHoms_iff.mpr hypar⟩
      have hcast := pairZFun_castR (S := ↥sixInt) N (x : Additive ↥(Gamma0 N) →+ ℤ) y
      rw [ModularCurve.PDPairing.pairZ_apply] at hc
      rw [hc] at hcast

      have hsc : 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt)
          ((6 : ↥sixInt) ^ k • (z : Additive ↥(Gamma0 N) →+ ↥sixInt)) = p * (c : ↥sixInt) := by
        rw [← hιdef] at hcast
        rw [← hy]
        exact_mod_cast hcast.symm
      rw [pairD_smul_right] at hsc
      refine ⟨⅟(6 : ↥sixInt) ^ k * c, ?_⟩
      calc 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z
          = (⅟(6 : ↥sixInt) ^ k * (6 : ↥sixInt) ^ k) *
              (96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z) := by
            rw [← mul_pow, invOf_mul_self, one_pow, one_mul]
        _ = ⅟(6 : ↥sixInt) ^ k * (96 * ((6 : ↥sixInt) ^ k *
              pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z)) := by ring
        _ = ⅟(6 : ↥sixInt) ^ k * (p * c) := by rw [hsc]
        _ = p * (⅟(6 : ↥sixInt) ^ k * c) := by ring

    choose μf hμf using hvals
    let μ' : ↥(parSub (Gamma0 N) ↥sixInt) →ₗ[↥sixInt] ↥sixInt :=
      { toFun := μf
        map_add' := by
          intro z₁ z₂
          apply mul_left_cancel₀ hpA
          rw [mul_add, ← hμf, ← hμf, ← hμf, Submodule.coe_add, pairD_add_right, mul_add]
        map_smul' := by
          intro r z
          apply mul_left_cancel₀ hpA
          rw [RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hμf, ← hμf, Submodule.coe_smul, pairD_smul_right]
          ring }

    obtain ⟨x', hx', -⟩ := hperf μ'
    have hrep : ∀ z : ↥(parSub (Gamma0 N) ↥sixInt),
        pairD (Gamma 4) (Gamma0 N) (((p : ↥sixInt) • x' : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt) z =
          pairD (Gamma 4) (Gamma0 N) (((96 : ↥sixInt) • xA : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt) z := by
      intro z
      rw [Submodule.coe_smul, Submodule.coe_smul, pairD_smul_left, pairD_smul_left, hx' z]
      exact (hμf z).symm
    have huniq := (hperf (pairDRight (Gamma 4) (Gamma0 N)
      (((96 : ↥sixInt) • xA : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt))).unique
      (y₁ := (p : ↥sixInt) • x') (y₂ := (96 : ↥sixInt) • xA)
      (fun z => by rw [pairDRight_apply]; exact hrep z) (fun z => by rw [pairDRight_apply])

    have hdiv : ∀ g : ↥(Gamma0 N), (p : ℤ) ∣ (x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) := by
      intro g
      have hg := congrArg (fun t : ↥(parSub (Gamma0 N) ↥sixInt) => (t : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g)) huniq
      simp only [Submodule.coe_smul, AddMonoidHom.smul_apply, smul_eq_mul] at hg

      have hxA : (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g) = ι ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g)) := rfl
      rw [hxA, hιdef] at hg
      apply int_dvd_of_sixInt_dvd p hp hp5 _ (⅟(96 : ↥sixInt) * (x' : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g))
      have : ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) : ↥sixInt) =
          ⅟(96 : ↥sixInt) * (96 * ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) : ↥sixInt)) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
      rw [this]
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, eq_intCast] at hg
      rw [← hg]
      ring
    exact exists_eq_smul_of_dvd_apply (p : ℤ) hp0 x hdiv
  refine ⟨left, ?_⟩

  intro y hy
  apply left y
  intro z
  have hswap : ModularCurve.PDPairing.pairZ N y z = - ModularCurve.PDPairing.pairZ N z y := by
    rw [ModularCurve.PDPairing.pairZ_apply, ModularCurve.PDPairing.pairZ_apply, ModularCurve.PDPairing.pairZFun_swap]
  rw [hswap]
  exact (dvd_neg).mpr (hy z)

end B12
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

end ModularCurve.PDPairing.TD
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace Glue
p2m_open "ModularCurve.PDPairing ModularCurve"

open ModularCurve.PDPairing.TD ModularCurve.PDPairing.Schreier ModularCurve.Sanov ModularCurve.PDPairing.SanThree PDPairing.Cover
open scoped MatrixGroups

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex]

noncomputable scoped instance fintypeVΦ : Fintype (VΦ Φ) := Fintype.ofFinite _

noncomputable def mV : ℕ := Fintype.card (VΦ Φ)

noncomputable def eV : VΦ Φ ≃ Fin (mV Φ) := Fintype.equivFin (VΦ Φ)

theorem mV_pos : 0 < mV Φ := Fintype.card_pos_iff.mpr ⟨v0 Φ⟩

noncomputable def permL (i : Fin 2) : Equiv.Perm (Fin (mV Φ)) :=
  ((eV Φ).symm.trans (MulAction.toPerm (sanL i : ↥sanovSubgroup))).trans (eV Φ)

@[scoped simp] theorem permL_apply (i : Fin 2) (j : Fin (mV Φ)) :
    permL Φ i j = eV Φ (sanL i • (eV Φ).symm j) := rfl

theorem permL_eV (i : Fin 2) (v : VΦ Φ) : permL Φ i (eV Φ v) = eV Φ (sanL i • v) := by
  rw [permL_apply, Equiv.symm_apply_apply]

noncomputable def pstep (v : VΦ Φ) (hv : v ≠ v0 Φ) : VΦ Φ × Fin 2 × Bool :=
  (parentStep sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ) v hv).1

omit [Φ.FiniteIndex] in
theorem pstep_depth (v : VΦ Φ) (hv : v ≠ v0 Φ) :
    (treeT Φ).depth (pstep Φ v hv).1 < (treeT Φ).depth v :=
  (parentStep sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ) v hv).2.1

omit [Φ.FiniteIndex] in
theorem pstep_act (v : VΦ Φ) (hv : v ≠ v0 Φ) :
    act sanL ((pstep Φ v hv).2.1, (pstep Φ v hv).2.2) • (pstep Φ v hv).1 = v :=
  (parentStep sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ) v hv).2.2

omit [Φ.FiniteIndex] in
theorem pstep_true {v : VΦ Φ} {hv : v ≠ v0 Φ} (h : (pstep Φ v hv).2.2 = true) :
    sanL (pstep Φ v hv).2.1 • (pstep Φ v hv).1 = v := by
  have := pstep_act Φ v hv
  rwa [act, if_pos h] at this

omit [Φ.FiniteIndex] in
theorem pstep_false {v : VΦ Φ} {hv : v ≠ v0 Φ} (h : (pstep Φ v hv).2.2 = false) :
    sanL (pstep Φ v hv).2.1 • v = (pstep Φ v hv).1 := by
  have := pstep_act Φ v hv
  have h' : ¬ ((pstep Φ v hv).2.2 = true) := by rw [h]; exact Bool.false_ne_true
  rw [act, if_neg h'] at this
  exact (inv_smul_eq_iff.mp this).symm

noncomputable def treeDataOf : TreeData (mV Φ) where
  pa := permL Φ 0
  pb := permL Φ 1
  v₀ := eV Φ (v0 Φ)
  depth j := (treeT Φ).depth ((eV Φ).symm j)
  parent j hj :=
    let v := (eV Φ).symm j
    have hv : v ≠ v0 Φ := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
    (eV Φ (pstep Φ v hv).1, (pstep Φ v hv).2.1, (pstep Φ v hv).2.2)
  hpar j hj := by
    set v := (eV Φ).symm j with hvdef
    have hv : v ≠ v0 Φ := fun h => hj (by rw [← h, hvdef, Equiv.apply_symm_apply])
    have hj' : j = eV Φ v := by rw [hvdef, Equiv.apply_symm_apply]
    show (if (pstep Φ v hv).2.2
      then (if (pstep Φ v hv).2.1 = 0 then permL Φ 0 else permL Φ 1) (eV Φ (pstep Φ v hv).1) = j
      else (if (pstep Φ v hv).2.1 = 0 then permL Φ 0 else permL Φ 1) j = eV Φ (pstep Φ v hv).1)
    have hsel : ∀ i : Fin 2, (if i = 0 then permL Φ 0 else permL Φ 1) = permL Φ i := by
      intro i; fin_cases i <;> rfl
    rw [hsel]
    by_cases hd : (pstep Φ v hv).2.2 = true
    · rw [if_pos hd, permL_eV, pstep_true Φ hd, hj']
    · have hd' : (pstep Φ v hv).2.2 = false := Bool.eq_false_iff.mpr hd
      rw [if_neg hd, hj', permL_eV, pstep_false Φ hd']
  hdepth j hj := by
    show (treeT Φ).depth ((eV Φ).symm (eV Φ _)) < (treeT Φ).depth ((eV Φ).symm j)
    rw [Equiv.symm_apply_apply]
    exact pstep_depth Φ _ _

section CoverDict

open Function

abbrev CD : Type := CoverDart (mV Φ)

noncomputable abbrev G0 : Fatgraph (Finset.univ : Finset (CD Φ)) := coverFatgraph (mV Φ) (permL Φ 0) (permL Φ 1)

def cdU (d : CD Φ) : ↥(Finset.univ : Finset (CD Φ)) := ⟨d, Finset.mem_univ d⟩

@[scoped simp] theorem cdU_val (d : CD Φ) : ((cdU Φ d : ↥(Finset.univ : Finset (CD Φ))) : CD Φ) = d := rfl

theorem cdU_coe (x : ↥(Finset.univ : Finset (CD Φ))) : cdU Φ (x : CD Φ) = x := Subtype.ext rfl

theorem permL_symm_eV (i : Fin 2) (v : VΦ Φ) : (permL Φ i).symm (eV Φ v) = eV Φ ((sanL i)⁻¹ • v) := by
  rw [Equiv.symm_apply_eq, permL_eV, smul_inv_smul]

theorem fp_val (d : CD Φ) :
    (((G0 Φ).facePerm (cdU Φ d) : ↥(Finset.univ : Finset (CD Φ))) : CD Φ) =
      ((coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d).1,
        (finRotate 4).symm (coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d).2) := rfl

theorem fp_slot0 (v : VΦ Φ) : (G0 Φ).facePerm (cdU Φ (eV Φ v, 0)) = cdU Φ (eV Φ (sanL 0 • v), 0) := by
  apply Subtype.ext
  rw [fp_val]
  simp [coverPrtFun, cdU, finRotate]
  decide

theorem fp_slot3 (v : VΦ Φ) : (G0 Φ).facePerm (cdU Φ (eV Φ v, 3)) = cdU Φ (eV Φ (sanL 1 • v), 1) := by
  apply Subtype.ext
  rw [fp_val]
  simp [coverPrtFun, cdU, finRotate]
  decide

theorem fp_slot1 (v : VΦ Φ) : (G0 Φ).facePerm (cdU Φ (eV Φ v, 1)) = cdU Φ (eV Φ ((sanL 0)⁻¹ • v), 3) := by
  apply Subtype.ext
  rw [fp_val]
  simp [coverPrtFun, permL_symm_eV, cdU, finRotate]
  decide

theorem fp_slot2 (v : VΦ Φ) : (G0 Φ).facePerm (cdU Φ (eV Φ v, 2)) = cdU Φ (eV Φ ((sanL 1)⁻¹ • v), 2) := by
  apply Subtype.ext
  rw [fp_val]
  simp [coverPrtFun, permL_symm_eV, cdU, finRotate]
  decide

theorem fp_iter_slot0 (v : VΦ Φ) (k : ℕ) :
    ((G0 Φ).facePerm^[k]) (cdU Φ (eV Φ v, 0)) = cdU Φ (eV Φ ((sanL 0) ^ k • v), 0) := by
  induction k generalizing v with
  | zero => rw [iterate_zero_apply, pow_zero, one_smul]
  | succ k ih => rw [iterate_succ_apply', ih, fp_slot0, ← mul_smul, ← pow_succ']

theorem fp_iter_slot2 (v : VΦ Φ) (k : ℕ) :
    ((G0 Φ).facePerm^[k]) (cdU Φ (eV Φ v, 2)) = cdU Φ (eV Φ ((sanL 1)⁻¹ ^ k • v), 2) := by
  induction k generalizing v with
  | zero => rw [iterate_zero_apply, pow_zero, one_smul]
  | succ k ih => rw [iterate_succ_apply', ih, fp_slot2, ← mul_smul, ← pow_succ']

theorem fp_two_slot3 (v : VΦ Φ) :
    ((G0 Φ).facePerm^[2]) (cdU Φ (eV Φ v, 3)) = cdU Φ (eV Φ (faceGen 2 • v), 3) := by
  show (G0 Φ).facePerm ((G0 Φ).facePerm (cdU Φ (eV Φ v, 3))) = _
  rw [fp_slot3, fp_slot1, ← mul_smul, faceGen_two]

theorem fp_iter_slot3_even (v : VΦ Φ) (k : ℕ) :
    ((G0 Φ).facePerm^[2 * k]) (cdU Φ (eV Φ v, 3)) = cdU Φ (eV Φ (faceGen 2 ^ k • v), 3) := by
  induction k generalizing v with
  | zero => rw [Nat.mul_zero, iterate_zero_apply, pow_zero, one_smul]
  | succ k ih =>
    rw [Nat.mul_succ, iterate_add_apply, fp_two_slot3, ih, ← mul_smul, ← pow_succ]

theorem fp_iter_slot3_odd (v : VΦ Φ) (k : ℕ) :
    ((G0 Φ).facePerm^[2 * k + 1]) (cdU Φ (eV Φ v, 3)) = cdU Φ (eV Φ (sanL 1 • faceGen 2 ^ k • v), 1) := by
  rw [iterate_succ_apply', fp_iter_slot3_even, fp_slot3]

theorem cdU_eV_injective (s : Fin 4) : Injective (fun v : VΦ Φ => cdU Φ (eV Φ v, s)) := by
  intro v w h
  have := congrArg (fun x : ↥(Finset.univ : Finset (CD Φ)) => (x : CD Φ).1) h
  exact (eV Φ).injective this

theorem mem_periodicPts_fp (x : ↥(Finset.univ : Finset (CD Φ))) : x ∈ periodicPts (G0 Φ).facePerm := by
  refine ⟨orderOf (G0 Φ).facePerm, orderOf_pos _, ?_⟩
  show IsPeriodicPt _ _ _
  rw [IsPeriodicPt, IsFixedPt, ← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

theorem minimalPeriod_slot0 (v : VΦ Φ) : minimalPeriod (G0 Φ).facePerm (cdU Φ (eV Φ v, 0)) = faceLen Φ 0 v := by
  unfold faceLen
  rw [faceGen_zero]
  exact minimalPeriod_semiconj (fun v : VΦ Φ => cdU Φ (eV Φ v, 0)) (cdU_eV_injective Φ 0) (fun w => sanovBasis 0 • w) _
    (fun w => (fp_slot0 Φ w).symm) v

theorem minimalPeriod_slot2 (v : VΦ Φ) : minimalPeriod (G0 Φ).facePerm (cdU Φ (eV Φ v, 2)) = faceLen Φ 1 v := by
  unfold faceLen
  rw [faceGen_one]
  exact minimalPeriod_semiconj (fun v : VΦ Φ => cdU Φ (eV Φ v, 2)) (cdU_eV_injective Φ 2) (fun w => (sanovBasis 1)⁻¹ • w) _
    (fun w => (fp_slot2 Φ w).symm) v

theorem minimalPeriod_slot3 (v : VΦ Φ) : minimalPeriod (G0 Φ).facePerm (cdU Φ (eV Φ v, 3)) = 2 * faceLen Φ 2 v := by
  set x := cdU Φ (eV Φ v, 3) with hx
  have h2 : minimalPeriod ((G0 Φ).facePerm^[2]) x = faceLen Φ 2 v := by
    unfold faceLen
    exact minimalPeriod_semiconj (fun v : VΦ Φ => cdU Φ (eV Φ v, 3)) (cdU_eV_injective Φ 3) (fun w => faceGen 2 • w) _
      (fun w => (fp_two_slot3 Φ w).symm) v
  have hper := mem_periodicPts_fp Φ x

  obtain ⟨j, hj⟩ : Even (minimalPeriod (G0 Φ).facePerm x) := by
    rcases Nat.even_or_odd (minimalPeriod (G0 Φ).facePerm x) with h | ⟨j, hj⟩
    · exact h
    · exfalso
      have hfix := iterate_minimalPeriod (f := (G0 Φ).facePerm) (x := x)
      rw [hj, hx, fp_iter_slot3_odd] at hfix
      have := congrArg (fun y : ↥(Finset.univ : Finset (CD Φ)) => (y : CD Φ).2) hfix
      simp [cdU] at this
  have hdiv := minimalPeriod_iterate_eq_div_gcd' (n := 2) hper
  rw [h2, hj, ← two_mul, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ two_pos] at hdiv
  rw [hj, ← two_mul, hdiv]

variable {R : Type*} [CommRing R]

noncomputable def dval (c : VΦ Φ → Fin 2 → R) (d : CD Φ) : R :=
  if d.2 = 0 then c ((eV Φ).symm d.1) 0
  else if d.2 = 1 then -c ((sanL 0)⁻¹ • (eV Φ).symm d.1) 0
  else if d.2 = 2 then -c ((sanL 1)⁻¹ • (eV Φ).symm d.1) 1
  else c ((eV Φ).symm d.1) 1

@[scoped simp] theorem dval_slot0 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : dval Φ c (eV Φ v, 0) = c v 0 := by
  simp [dval]

@[scoped simp] theorem dval_slot1 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : dval Φ c (eV Φ v, 1) = -c ((sanL 0)⁻¹ • v) 0 := by
  simp [dval]

@[scoped simp] theorem dval_slot2 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : dval Φ c (eV Φ v, 2) = -c ((sanL 1)⁻¹ • v) 1 := by
  simp [dval]

@[scoped simp] theorem dval_slot3 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : dval Φ c (eV Φ v, 3) = c v 1 := by
  simp [dval]

theorem dval_prt (c : VΦ Φ → Fin 2 → R) (d : CD Φ) :
    dval Φ c (coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d) = -dval Φ c d := by
  obtain ⟨j, s⟩ := d
  obtain ⟨v, rfl⟩ := (eV Φ).surjective j
  fin_cases s <;> simp [coverPrtFun, permL_symm_eV]

theorem dval_add (c c' : VΦ Φ → Fin 2 → R) (d : CD Φ) : dval Φ (c + c') d = dval Φ c d + dval Φ c' d := by
  unfold dval
  split_ifs <;> simp <;> ring

theorem dval_smul (r : R) (c : VΦ Φ → Fin 2 → R) (d : CD Φ) : dval Φ (r • c) d = r * dval Φ c d := by
  unfold dval
  split_ifs <;> simp

omit [Φ.FiniteIndex] in
theorem walkSum_nil' (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : walkSum Φ c v [] = 0 := rfl

omit [Φ.FiniteIndex] in
theorem walkSum_cons' (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (p : Fin 2 × Bool) (l : List (Fin 2 × Bool)) :
    walkSum Φ c v (p :: l) = sval Φ c (wprod sanL l • v) p + walkSum Φ c v l := rfl

omit [Φ.FiniteIndex] in
theorem walkSum_append' (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (l₁ l₂ : List (Fin 2 × Bool)) :
    walkSum Φ c v (l₁ ++ l₂) = walkSum Φ c (wprod sanL l₂ • v) l₁ + walkSum Φ c v l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, walkSum_nil', zero_add]
  | cons p l₁ ih => rw [List.cons_append, walkSum_cons', walkSum_cons', ih, wprod_append, mul_smul, add_assoc]

theorem faceWord_zero (i : Fin 3) : faceWord i 0 = [] := by simp [faceWord]

theorem faceWord_succ (i : Fin 3) (k : ℕ) : faceWord i (k + 1) = faceRound i ++ faceWord i k := by
  simp [faceWord, List.replicate_succ]

noncomputable def roundVal (i : Fin 3) (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) : R := walkSum Φ c w (faceRound i)

omit [Φ.FiniteIndex] in
theorem walkSum_faceWord (i : Fin 3) (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord i k) = ∑ j ∈ Finset.range k, roundVal Φ i c (faceGen i ^ j • v) := by
  induction k with
  | zero => rw [faceWord_zero, walkSum_nil', Finset.sum_range_zero]
  | succ k ih => rw [faceWord_succ, walkSum_append', wprod_faceWord, ih, Finset.sum_range_succ, add_comm]; rfl

omit [Φ.FiniteIndex] in
theorem roundVal_zero (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) : roundVal Φ 0 c w = c w 0 := by
  simp [roundVal, faceRound, walkSum, sval, wprod_nil]

omit [Φ.FiniteIndex] in
theorem roundVal_one (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) : roundVal Φ 1 c w = -c ((sanL 1)⁻¹ • w) 1 := by
  simp [roundVal, faceRound, walkSum, sval, wprod_nil]

omit [Φ.FiniteIndex] in
theorem roundVal_two (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) :
    roundVal Φ 2 c w = -c ((sanL 0)⁻¹ • sanL 1 • w) 0 + c w 1 := by
  simp [roundVal, faceRound, walkSum, sval, wprod_cons, wprod_nil, act]

def rlen : Fin 3 → ℕ := ![1, 1, 2]

def sslot : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 3

noncomputable def sdart (i : Fin 3) (v : VΦ Φ) : ↥(Finset.univ : Finset (CD Φ)) := cdU Φ (eV Φ v, sslot i)

theorem sdart_zero (v : VΦ Φ) : sdart Φ 0 v = cdU Φ (eV Φ v, 0) := rfl
theorem sdart_one (v : VΦ Φ) : sdart Φ 1 v = cdU Φ (eV Φ v, 2) := rfl
theorem sdart_two (v : VΦ Φ) : sdart Φ 2 v = cdU Φ (eV Φ v, 3) := rfl

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ r ∈ Finset.range (2 * k), f r = ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

theorem walkSum_faceWord_eq_orbit0 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 0 k) = ∑ r ∈ Finset.range k, dval Φ c (((G0 Φ).facePerm^[r]) (sdart Φ 0 v) : CD Φ) := by
  rw [walkSum_faceWord, sdart_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [roundVal_zero, fp_iter_slot0, cdU_val, dval_slot0, faceGen_zero]

theorem walkSum_faceWord_eq_orbit1 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 1 k) = ∑ r ∈ Finset.range k, dval Φ c (((G0 Φ).facePerm^[r]) (sdart Φ 1 v) : CD Φ) := by
  rw [walkSum_faceWord, sdart_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [roundVal_one, fp_iter_slot2, cdU_val, dval_slot2, faceGen_one]

theorem walkSum_faceWord_eq_orbit2 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 2 k) = ∑ r ∈ Finset.range (2 * k), dval Φ c (((G0 Φ).facePerm^[r]) (sdart Φ 2 v) : CD Φ) := by
  rw [walkSum_faceWord, sdart_two, sum_range_two_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [roundVal_two, fp_iter_slot3_even, fp_iter_slot3_odd, cdU_val, cdU_val, dval_slot3, dval_slot1, add_comm]

end CoverDict
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section PairDict

open Function

variable {R : Type*} [CommRing R]

noncomputable def Fd (c c' : VΦ Φ → Fin 2 → R) (d d' : CD Φ) : R :=
  dval Φ c d * dval Φ c' d' - dval Φ c' d * dval Φ c d'

theorem Fd_swap (c c' : VΦ Φ → Fin 2 → R) (d d' : CD Φ) : Fd Φ c c' d' d = -Fd Φ c c' d d' := by
  unfold Fd; ring

noncomputable def dseq (i : Fin 3) (v : VΦ Φ) (r : ℕ) : CD Φ := (((G0 Φ).facePerm^[r]) (sdart Φ i v) : CD Φ)

noncomputable def CS (c : VΦ Φ → Fin 2 → R) (i : Fin 3) (v : VΦ Φ) (L : ℕ) : R :=
  ∑ r ∈ Finset.range L, dval Φ c (dseq Φ i v r)

noncomputable def CP (c c' : VΦ Φ → Fin 2 → R) (i : Fin 3) (v : VΦ Φ) (L : ℕ) : R :=
  ∑ b ∈ Finset.range L, ∑ a ∈ Finset.range b, Fd Φ c c' (dseq Φ i v a) (dseq Φ i v b)

theorem CS_succ (c : VΦ Φ → Fin 2 → R) (i : Fin 3) (v : VΦ Φ) (L : ℕ) :
    CS Φ c i v (L + 1) = CS Φ c i v L + dval Φ c (dseq Φ i v L) := by
  rw [CS, Finset.sum_range_succ, ← CS]

theorem CP_succ (c c' : VΦ Φ → Fin 2 → R) (i : Fin 3) (v : VΦ Φ) (L : ℕ) :
    CP Φ c c' i v (L + 1) =
      CP Φ c c' i v L + (CS Φ c i v L * dval Φ c' (dseq Φ i v L) - CS Φ c' i v L * dval Φ c (dseq Φ i v L)) := by
  rw [CP, Finset.sum_range_succ, ← CP]
  congr 1
  simp only [Fd, Finset.sum_sub_distrib, CS, Finset.sum_mul]

variable (hΦs : Φ ≤ sanovSubgroup)

omit [Φ.FiniteIndex] in
theorem letters_append' (v : VΦ Φ) (l₁ l₂ : List (Fin 2 × Bool)) :
    letters Φ hΦs v (l₁ ++ l₂) = letters Φ hΦs (wprod sanL l₂ • v) l₁ ++ letters Φ hΦs v l₂ := by
  induction l₁ with
  | nil => rfl
  | cons p l₁ ih => rw [List.cons_append, letters, letters, ih, wprod_append, mul_smul, List.cons_append]

omit [Φ.FiniteIndex] in
theorem char_prod_letters (χ : Additive Φ →+ R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    χ (Additive.ofMul (letters Φ hΦs v l).prod) = walkSum Φ (edgeVal Φ hΦs χ) v l := by
  rw [prod_letters, char_wordWalk_eq_walkSum]

omit [Φ.FiniteIndex] in
theorem pairSum_letters_single (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (p : Fin 2 × Bool) :
    pairSum φ ψ (letters Φ hΦs w [p]) = 0 := by
  simp [letters, pairSum]

omit [Φ.FiniteIndex] in
theorem pairSum_letters_pair (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (p q : Fin 2 × Bool) :
    pairSum φ ψ (letters Φ hΦs w [p, q]) =
      omega φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx (act sanL q • w) p)) (stabEquiv Φ hΦs ((treeT Φ).sx w q)) := by
  simp [letters, pairSum, wprod_cons, wprod_nil]

theorem walkSum_faceWord_eq_CS0 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 0 k) = CS Φ c 0 v k := walkSum_faceWord_eq_orbit0 Φ c v k

theorem walkSum_faceWord_eq_CS1 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 1 k) = CS Φ c 1 v k := walkSum_faceWord_eq_orbit1 Φ c v k

theorem walkSum_faceWord_eq_CS2 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    walkSum Φ c v (faceWord 2 k) = CS Φ c 2 v (2 * k) := walkSum_faceWord_eq_orbit2 Φ c v k

theorem roundVal_eq_CS_diff0 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    roundVal Φ 0 c (faceGen 0 ^ k • v) = CS Φ c 0 v (k + 1) - CS Φ c 0 v k := by
  have h := walkSum_faceWord_eq_CS0 Φ c v (k + 1)
  rw [faceWord_succ, walkSum_append', wprod_faceWord, walkSum_faceWord_eq_CS0] at h
  rw [roundVal]
  linear_combination h

theorem roundVal_eq_CS_diff1 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    roundVal Φ 1 c (faceGen 1 ^ k • v) = CS Φ c 1 v (k + 1) - CS Φ c 1 v k := by
  have h := walkSum_faceWord_eq_CS1 Φ c v (k + 1)
  rw [faceWord_succ, walkSum_append', wprod_faceWord, walkSum_faceWord_eq_CS1] at h
  rw [roundVal]
  linear_combination h

theorem roundVal_eq_CS_diff2 (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (k : ℕ) :
    roundVal Φ 2 c (faceGen 2 ^ k • v) = CS Φ c 2 v (2 * (k + 1)) - CS Φ c 2 v (2 * k) := by
  have h := walkSum_faceWord_eq_CS2 Φ c v (k + 1)
  rw [faceWord_succ, walkSum_append', wprod_faceWord, walkSum_faceWord_eq_CS2] at h
  rw [roundVal]
  linear_combination h

theorem pairSum_letters_faceWord0 (φ ψ : Additive Φ →+ R) (v : VΦ Φ) (k : ℕ) :
    pairSum φ ψ (letters Φ hΦs v (faceWord 0 k)) = -CP Φ (edgeVal Φ hΦs φ) (edgeVal Φ hΦs ψ) 0 v k := by
  induction k with
  | zero => simp [faceWord_zero, letters, pairSum, CP]
  | succ k ih =>
    rw [faceWord_succ, letters_append', pairSum_append, ih, wprod_faceWord, omega, char_prod_letters, char_prod_letters,
      char_prod_letters, char_prod_letters, walkSum_faceWord_eq_CS0, walkSum_faceWord_eq_CS0]
    change pairSum φ ψ (letters Φ hΦs (faceGen 0 ^ k • v) (faceRound 0)) + _ +
      (roundVal Φ 0 (edgeVal Φ hΦs φ) (faceGen 0 ^ k • v) * _ - roundVal Φ 0 (edgeVal Φ hΦs ψ) (faceGen 0 ^ k • v) * _) = _
    rw [roundVal_eq_CS_diff0, roundVal_eq_CS_diff0, show faceRound 0 = [(0, true)] from rfl, pairSum_letters_single,
      CP_succ, CS_succ, CS_succ]
    ring

theorem pairSum_letters_faceWord1 (φ ψ : Additive Φ →+ R) (v : VΦ Φ) (k : ℕ) :
    pairSum φ ψ (letters Φ hΦs v (faceWord 1 k)) = -CP Φ (edgeVal Φ hΦs φ) (edgeVal Φ hΦs ψ) 1 v k := by
  induction k with
  | zero => simp [faceWord_zero, letters, pairSum, CP]
  | succ k ih =>
    rw [faceWord_succ, letters_append', pairSum_append, ih, wprod_faceWord, omega, char_prod_letters, char_prod_letters,
      char_prod_letters, char_prod_letters, walkSum_faceWord_eq_CS1, walkSum_faceWord_eq_CS1]
    change pairSum φ ψ (letters Φ hΦs (faceGen 1 ^ k • v) (faceRound 1)) + _ +
      (roundVal Φ 1 (edgeVal Φ hΦs φ) (faceGen 1 ^ k • v) * _ - roundVal Φ 1 (edgeVal Φ hΦs ψ) (faceGen 1 ^ k • v) * _) = _
    rw [roundVal_eq_CS_diff1, roundVal_eq_CS_diff1, show faceRound 1 = [(1, false)] from rfl, pairSum_letters_single,
      CP_succ, CS_succ, CS_succ]
    ring

theorem pairSum_letters_faceWord2 (φ ψ : Additive Φ →+ R) (v : VΦ Φ) (k : ℕ) :
    pairSum φ ψ (letters Φ hΦs v (faceWord 2 k)) = -CP Φ (edgeVal Φ hΦs φ) (edgeVal Φ hΦs ψ) 2 v (2 * k) := by
  induction k with
  | zero => simp [faceWord_zero, letters, pairSum, CP]
  | succ k ih =>
    rw [faceWord_succ, letters_append', pairSum_append, ih, wprod_faceWord, omega, char_prod_letters, char_prod_letters,
      char_prod_letters, char_prod_letters, walkSum_faceWord_eq_CS2, walkSum_faceWord_eq_CS2]
    change pairSum φ ψ (letters Φ hΦs (faceGen 2 ^ k • v) (faceRound 2)) + _ +
      (roundVal Φ 2 (edgeVal Φ hΦs φ) (faceGen 2 ^ k • v) * _ - roundVal Φ 2 (edgeVal Φ hΦs ψ) (faceGen 2 ^ k • v) * _) = _
    rw [roundVal_eq_CS_diff2, roundVal_eq_CS_diff2, show faceRound 2 = [(0, false), (1, true)] from rfl,
      pairSum_letters_pair, omega_letter, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, CP_succ, CP_succ, CS_succ, CS_succ,
      CS_succ, CS_succ]
    have hd0 : dseq Φ 2 v (2 * k) = (eV Φ (faceGen 2 ^ k • v), 3) := by
      rw [dseq, sdart_two, fp_iter_slot3_even, cdU_val]
    have hd1 : dseq Φ 2 v (2 * k + 1) = (eV Φ (sanL 1 • faceGen 2 ^ k • v), 1) := by
      rw [dseq, sdart_two, fp_iter_slot3_odd, cdU_val]
    rw [hd0, hd1]
    simp only [dval_slot3, dval_slot1, sval, act, ↓reduceIte, Bool.false_eq_true]
    ring

end PairDict
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section OrbitTools

open Function

variable {R : Type*} [CommRing R]

noncomputable def hD (hΦs : Φ ≤ sanovSubgroup) {M : Type*} (h : Φ → M) (d : CD Φ) : M :=
  if d.2 = 0 then h (stabEquiv Φ hΦs ((treeT Φ).sx ((eV Φ).symm d.1) (0, true)))
  else if d.2 = 1 then h (stabEquiv Φ hΦs ((treeT Φ).sx ((eV Φ).symm d.1) (0, false)))
  else if d.2 = 2 then h (stabEquiv Φ hΦs ((treeT Φ).sx ((eV Φ).symm d.1) (1, false)))
  else h (stabEquiv Φ hΦs ((treeT Φ).sx ((eV Φ).symm d.1) (1, true)))

variable (hΦs : Φ ≤ sanovSubgroup)

@[scoped simp] theorem hD_slot0 {M : Type*} (h : Φ → M) (w : VΦ Φ) :
    hD Φ hΦs h (eV Φ w, 0) = h (stabEquiv Φ hΦs ((treeT Φ).sx w (0, true))) := by simp [hD]
@[scoped simp] theorem hD_slot1 {M : Type*} (h : Φ → M) (w : VΦ Φ) :
    hD Φ hΦs h (eV Φ w, 1) = h (stabEquiv Φ hΦs ((treeT Φ).sx w (0, false))) := by simp [hD]
@[scoped simp] theorem hD_slot2 {M : Type*} (h : Φ → M) (w : VΦ Φ) :
    hD Φ hΦs h (eV Φ w, 2) = h (stabEquiv Φ hΦs ((treeT Φ).sx w (1, false))) := by simp [hD]
@[scoped simp] theorem hD_slot3 {M : Type*} (h : Φ → M) (w : VΦ Φ) :
    hD Φ hΦs h (eV Φ w, 3) = h (stabEquiv Φ hΦs ((treeT Φ).sx w (1, true))) := by simp [hD]

omit [Φ.FiniteIndex] in
theorem map_letters_append {M : Type*} [AddCommMonoid M] (h : Φ → M) (v : VΦ Φ) (l₁ l₂ : List (Fin 2 × Bool)) :
    ((letters Φ hΦs v (l₁ ++ l₂)).map h).sum =
      ((letters Φ hΦs (wprod sanL l₂ • v) l₁).map h).sum + ((letters Φ hΦs v l₂).map h).sum := by
  rw [letters_append', List.map_append, List.sum_append]

theorem sum_letters_faceWord0 {M : Type*} [AddCommMonoid M] (h : Φ → M) (v : VΦ Φ) (k : ℕ) :
    ((letters Φ hΦs v (faceWord 0 k)).map h).sum = ∑ r ∈ Finset.range k, hD Φ hΦs h (dseq Φ 0 v r) := by
  induction k with
  | zero => simp [faceWord_zero, letters]
  | succ k ih =>
    rw [faceWord_succ, map_letters_append, ih, wprod_faceWord, Finset.sum_range_succ, add_comm,
      show faceRound 0 = [(0, true)] from rfl]
    simp only [letters, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wprod_nil, one_smul]
    rw [dseq, sdart_zero, fp_iter_slot0, cdU_val, hD_slot0, faceGen_zero]

theorem sum_letters_faceWord1 {M : Type*} [AddCommMonoid M] (h : Φ → M) (v : VΦ Φ) (k : ℕ) :
    ((letters Φ hΦs v (faceWord 1 k)).map h).sum = ∑ r ∈ Finset.range k, hD Φ hΦs h (dseq Φ 1 v r) := by
  induction k with
  | zero => simp [faceWord_zero, letters]
  | succ k ih =>
    rw [faceWord_succ, map_letters_append, ih, wprod_faceWord, Finset.sum_range_succ, add_comm,
      show faceRound 1 = [(1, false)] from rfl]
    simp only [letters, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wprod_nil, one_smul]
    rw [dseq, sdart_one, fp_iter_slot2, cdU_val, hD_slot2, faceGen_one]

theorem sum_letters_faceWord2 {M : Type*} [AddCommMonoid M] (h : Φ → M) (v : VΦ Φ) (k : ℕ) :
    ((letters Φ hΦs v (faceWord 2 k)).map h).sum = ∑ r ∈ Finset.range (2 * k), hD Φ hΦs h (dseq Φ 2 v r) := by
  induction k with
  | zero => simp [faceWord_zero, letters]
  | succ k ih =>
    rw [faceWord_succ, map_letters_append, ih, wprod_faceWord, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, show faceRound 2 = [(0, false), (1, true)] from rfl]
    simp only [letters, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wprod_nil, one_smul,
      wprod_cons, mul_one, act, ↓reduceIte]
    rw [dseq, dseq, sdart_two, fp_iter_slot3_even, fp_iter_slot3_odd, cdU_val, cdU_val, hD_slot3, hD_slot1]
    abel

theorem hD_prt (h : Φ → R)
    (hodd : ∀ (w : VΦ Φ) (i : Fin 2), h (stabEquiv Φ hΦs ((treeT Φ).sx w (i, false))) =
      -h (stabEquiv Φ hΦs ((treeT Φ).sx ((sanL i)⁻¹ • w) (i, true)))) (d : CD Φ) :
    hD Φ hΦs h (coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d) = -hD Φ hΦs h d := by
  obtain ⟨j, s⟩ := d
  obtain ⟨w, rfl⟩ := (eV Φ).surjective j
  fin_cases s
  · simp [coverPrtFun, hodd]
  · simp [coverPrtFun, permL_symm_eV, hodd]
  · simp [coverPrtFun, permL_symm_eV, hodd]
  · simp [coverPrtFun, hodd]

theorem orbitSum_apply {X : Type*} {M : Type*} [AddCommMonoid M] (σ : X → X) (g : X → M) (x : X)
    (hx : x ∈ periodicPts σ) :
    ∑ r ∈ Finset.range (minimalPeriod σ (σ x)), g (σ^[r] (σ x)) = ∑ r ∈ Finset.range (minimalPeriod σ x), g (σ^[r] x) := by
  rw [minimalPeriod_apply hx]
  obtain ⟨m, hm⟩ : ∃ m, minimalPeriod σ x = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (minimalPeriod_pos_of_mem_periodicPts hx).ne'
  have hfix : σ^[m + 1] x = x := by rw [← hm, iterate_minimalPeriod]
  rw [hm]
  simp_rw [← iterate_succ_apply σ _ x]
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun r => g (σ^[r] x)), hfix, iterate_zero_apply]

theorem iterate_mem_periodicPts {X : Type*} (σ : X → X) (x : X) (hx : x ∈ periodicPts σ) (s : ℕ) :
    σ^[s] x ∈ periodicPts σ :=
  mk_mem_periodicPts (minimalPeriod_pos_of_mem_periodicPts hx) ((isPeriodicPt_minimalPeriod σ x).apply_iterate s)

theorem orbitSum_iterate {X : Type*} {M : Type*} [AddCommMonoid M] (σ : X → X) (g : X → M) (x : X)
    (hx : x ∈ periodicPts σ) (s : ℕ) :
    ∑ r ∈ Finset.range (minimalPeriod σ (σ^[s] x)), g (σ^[r] (σ^[s] x)) =
      ∑ r ∈ Finset.range (minimalPeriod σ x), g (σ^[r] x) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [iterate_succ_apply', orbitSum_apply σ g _ (iterate_mem_periodicPts σ x hx s), ih]

theorem pairOrbitSum_apply {X : Type*} (σ : X → X) (F G : X → R) (x : X) (hx : x ∈ periodicPts σ)
    (hF : ∑ r ∈ Finset.range (minimalPeriod σ x), F (σ^[r] x) = 0)
    (hG : ∑ r ∈ Finset.range (minimalPeriod σ x), G (σ^[r] x) = 0) :
    ∑ b ∈ Finset.range (minimalPeriod σ (σ x)), ∑ a ∈ Finset.range b,
        (F (σ^[a] (σ x)) * G (σ^[b] (σ x)) - G (σ^[a] (σ x)) * F (σ^[b] (σ x))) =
      ∑ b ∈ Finset.range (minimalPeriod σ x), ∑ a ∈ Finset.range b,
        (F (σ^[a] x) * G (σ^[b] x) - G (σ^[a] x) * F (σ^[b] x)) := by
  rw [minimalPeriod_apply hx]
  obtain ⟨m, hm⟩ : ∃ m, minimalPeriod σ x = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (minimalPeriod_pos_of_mem_periodicPts hx).ne'
  rw [hm] at hF hG ⊢
  have hu : σ^[m + 1] x = x := by rw [← hm, iterate_minimalPeriod]
  simp_rw [← iterate_succ_apply σ]

  rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_zero, add_zero]
  simp_rw [Finset.sum_range_succ' (fun a => F (σ^[a] x) * G (σ^[_ + 1] x) - G (σ^[a] x) * F (σ^[_ + 1] x))]
  rw [Finset.sum_add_distrib, hu, iterate_zero_apply]
  rw [Finset.sum_range_succ'] at hF hG
  rw [iterate_zero_apply] at hF hG
  have hF' : ∑ b ∈ Finset.range m, F (σ^[b + 1] x) = -F x := by linear_combination hF
  have hG' : ∑ b ∈ Finset.range m, G (σ^[b + 1] x) = -G x := by linear_combination hG
  have h1 : ∑ a ∈ Finset.range m, (F (σ^[a + 1] x) * G x - G (σ^[a + 1] x) * F x) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hF', hG']; ring
  have h2 : ∑ b ∈ Finset.range m, (F x * G (σ^[b + 1] x) - G x * F (σ^[b + 1] x)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hF', hG']; ring
  rw [h1, h2]

theorem pairOrbitSum_iterate {X : Type*} (σ : X → X) (F G : X → R) (x : X) (hx : x ∈ periodicPts σ)
    (hF : ∑ r ∈ Finset.range (minimalPeriod σ x), F (σ^[r] x) = 0)
    (hG : ∑ r ∈ Finset.range (minimalPeriod σ x), G (σ^[r] x) = 0) (s : ℕ) :
    ∑ b ∈ Finset.range (minimalPeriod σ (σ^[s] x)), ∑ a ∈ Finset.range b,
        (F (σ^[a] (σ^[s] x)) * G (σ^[b] (σ^[s] x)) - G (σ^[a] (σ^[s] x)) * F (σ^[b] (σ^[s] x))) =
      ∑ b ∈ Finset.range (minimalPeriod σ x), ∑ a ∈ Finset.range b,
        (F (σ^[a] x) * G (σ^[b] x) - G (σ^[a] x) * F (σ^[b] x)) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hxs := iterate_mem_periodicPts σ x hx s
    have hFs : ∑ r ∈ Finset.range (minimalPeriod σ (σ^[s] x)), F (σ^[r] (σ^[s] x)) = 0 := by
      rw [orbitSum_iterate σ F x hx s, hF]
    have hGs : ∑ r ∈ Finset.range (minimalPeriod σ (σ^[s] x)), G (σ^[r] (σ^[s] x)) = 0 := by
      rw [orbitSum_iterate σ G x hx s, hG]
    rw [iterate_succ_apply', pairOrbitSum_apply σ F G _ hxs hFs hGs, ih]

end OrbitTools
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section TreeDarts

def fslot : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 3

noncomputable def fdart (w : VΦ Φ) (i : Fin 2) : CD Φ := (eV Φ w, fslot i)

theorem fdart_injective {w w' : VΦ Φ} {i i' : Fin 2} (h : fdart Φ w i = fdart Φ w' i') : w = w' ∧ i = i' := by
  simp only [fdart, Prod.mk.injEq] at h
  refine ⟨(eV Φ).injective h.1, ?_⟩
  have h2 := h.2
  fin_cases i <;> fin_cases i' <;> simp_all [fslot]

theorem fdart_slot_ne (w w' : VΦ Φ) (i i' : Fin 2) :
    fdart Φ w i ≠ coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (fdart Φ w' i') := by
  intro h
  have h2 := congrArg Prod.snd h
  fin_cases i <;> fin_cases i' <;> simp [fdart, fslot, coverPrtFun] at h2

local notation "prtC" => coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1)

noncomputable def ptail (v : VΦ Φ) (hv : v ≠ v0 Φ) : VΦ Φ := if (pstep Φ v hv).2.2 then (pstep Φ v hv).1 else v

theorem treeDataOf_v₀ : (treeDataOf Φ).v₀ = eV Φ (v0 Φ) := rfl

theorem eV_ne_v₀ {v : VΦ Φ} (hv : v ≠ v0 Φ) : eV Φ v ≠ (treeDataOf Φ).v₀ :=
  fun h => hv ((eV Φ).injective h)

theorem ne_v0_of_eV_ne {v : VΦ Φ} (hj : eV Φ v ≠ (treeDataOf Φ).v₀) : v ≠ v0 Φ :=
  fun h => hj (by rw [h]; rfl)

theorem parent_treeDataOf (v : VΦ Φ) (hv : v ≠ v0 Φ) (hj : eV Φ v ≠ (treeDataOf Φ).v₀) :
    (treeDataOf Φ).parent (eV Φ v) hj = (eV Φ (pstep Φ v hv).1, (pstep Φ v hv).2.1, (pstep Φ v hv).2.2) := by
  have key : ∀ (w : VΦ Φ) (hw : w ≠ v0 Φ), w = v →
      ((eV Φ (pstep Φ w hw).1, (pstep Φ w hw).2.1, (pstep Φ w hw).2.2) : Fin (mV Φ) × Fin 2 × Bool) =
        (eV Φ (pstep Φ v hv).1, (pstep Φ v hv).2.1, (pstep Φ v hv).2.2) := by
    rintro w hw rfl; rfl
  exact key ((eV Φ).symm (eV Φ v)) _ (Equiv.symm_apply_apply _ _)

theorem parentDart_def (j : Fin (mV Φ)) (hj : j ≠ (treeDataOf Φ).v₀) :
    (treeDataOf Φ).parentDart j hj = prtC ((treeDataOf Φ).childDart j hj) := rfl

theorem prtC_fdart0 (u : VΦ Φ) : prtC (fdart Φ u 0) = (eV Φ (sanL 0 • u), 1) := by
  rw [← permL_eV]; rfl

theorem prtC_fdart1 (u : VΦ Φ) : prtC (fdart Φ u 1) = (eV Φ (sanL 1 • u), 2) := by
  rw [← permL_eV]; rfl

theorem childDart_eV (v : VΦ Φ) (hv : v ≠ v0 Φ) (hj : eV Φ v ≠ (treeDataOf Φ).v₀) :
    (treeDataOf Φ).childDart (eV Φ v) hj =
      if (pstep Φ v hv).2.2 then prtC (fdart Φ (ptail Φ v hv) (pstep Φ v hv).2.1)
      else fdart Φ (ptail Φ v hv) (pstep Φ v hv).2.1 := by
  unfold TreeData.childDart
  rw [parent_treeDataOf Φ v hv hj]
  dsimp only
  by_cases hd : (pstep Φ v hv).2.2 = true
  · have hu := pstep_true Φ hd
    rw [if_pos hd, ptail, if_pos hd]
    rcases Fin.exists_fin_two.mp ⟨(pstep Φ v hv).2.1, rfl⟩ with h0 | h1
    · rw [h0] at hu ⊢
      simp only [hd, ↓reduceIte, prtC_fdart0, hu]
    · rw [h1] at hu ⊢
      simp only [hd, ↓reduceIte, prtC_fdart1, hu]
      simp
  · have hd' : (pstep Φ v hv).2.2 = false := Bool.eq_false_iff.mpr hd
    rw [if_neg hd, ptail, if_neg hd]
    rcases Fin.exists_fin_two.mp ⟨(pstep Φ v hv).2.1, rfl⟩ with h0 | h1
    · rw [h0]; simp [hd', fdart, fslot]
    · rw [h1]; simp [hd', fdart, fslot]

theorem parentDart_eV (v : VΦ Φ) (hv : v ≠ v0 Φ) (hj : eV Φ v ≠ (treeDataOf Φ).v₀) :
    (treeDataOf Φ).parentDart (eV Φ v) hj =
      if (pstep Φ v hv).2.2 then fdart Φ (ptail Φ v hv) (pstep Φ v hv).2.1
      else prtC (fdart Φ (ptail Φ v hv) (pstep Φ v hv).2.1) := by
  rw [parentDart_def, childDart_eV Φ v hv hj]
  split_ifs with h
  · exact coverPrtFun_involutive _ _ _ _
  · rfl

omit [Φ.FiniteIndex] in

theorem tree_iff_ptail (w : VΦ Φ) (i : Fin 2) :
    (treeT Φ).tree w i = true ↔ ∃ (v : VΦ Φ) (hv : v ≠ v0 Φ), ptail Φ v hv = w ∧ (pstep Φ v hv).2.1 = i := by
  show treeBFS sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ) w i = true ↔ _
  rw [treeBFS_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rcases h with ⟨hd, hu, hi⟩ | ⟨hd, hvw, hi⟩
    · exact ⟨by rw [ptail, if_pos (show (pstep Φ v hv).2.2 = true from hd)]; exact hu, hi⟩
    · refine ⟨?_, hi⟩
      rw [ptail, if_neg (show ¬ (pstep Φ v hv).2.2 = true by rw [show (pstep Φ v hv).2.2 = false from hd]; decide)]
      exact hvw
  · rintro ⟨v, hv, hw, hi⟩
    refine ⟨v, hv, ?_⟩
    by_cases hd : (pstep Φ v hv).2.2 = true
    · left; rw [ptail, if_pos hd] at hw; exact ⟨hd, hw, hi⟩
    · right; rw [ptail, if_neg hd] at hw; exact ⟨Bool.eq_false_iff.mpr hd, hw, hi⟩

variable {t : Finset (CD Φ)}
  (hmem : ∀ d : CD Φ, d ∈ t ↔ ∀ (w : Fin (mV Φ)) (hw : w ≠ (treeDataOf Φ).v₀),
    d ≠ (treeDataOf Φ).childDart w hw ∧ d ≠ (treeDataOf Φ).parentDart w hw)
include hmem

theorem fdart_notMem_iff (w : VΦ Φ) (i : Fin 2) : fdart Φ w i ∉ t ↔ (treeT Φ).tree w i = true := by
  rw [tree_iff_ptail, hmem]
  push Not
  constructor
  · rintro ⟨j, hj, h⟩
    obtain ⟨v, rfl⟩ := (eV Φ).surjective j
    have hv : v ≠ v0 Φ := ne_v0_of_eV_ne Φ hj
    refine ⟨v, hv, ?_⟩
    rw [childDart_eV Φ v hv hj, parentDart_eV Φ v hv hj] at h
    by_cases hd : (pstep Φ v hv).2.2 = true
    · rw [if_pos hd, if_pos hd] at h
      have h' := h (fdart_slot_ne Φ _ _ _ _)
      exact ⟨(fdart_injective Φ h').1.symm, (fdart_injective Φ h').2.symm⟩
    · rw [if_neg hd, if_neg hd] at h
      have h' : fdart Φ w i = fdart Φ (ptail Φ v hv) (pstep Φ v hv).2.1 := by
        by_contra hne; exact fdart_slot_ne Φ _ _ _ _ (h hne)
      exact ⟨(fdart_injective Φ h').1.symm, (fdart_injective Φ h').2.symm⟩
  · rintro ⟨v, hv, hw, hi⟩
    refine ⟨eV Φ v, eV_ne_v₀ Φ hv, ?_⟩
    intro hne
    rw [childDart_eV Φ v hv (eV_ne_v₀ Φ hv), hw, hi] at hne
    rw [parentDart_eV Φ v hv (eV_ne_v₀ Φ hv), hw, hi]
    by_cases hd : (pstep Φ v hv).2.2 = true
    · rw [if_pos hd]
    · rw [if_neg hd] at hne; exact absurd rfl hne

theorem prt_mem_iff (d : CD Φ) : prtC d ∈ t ↔ d ∈ t := by
  rw [hmem, hmem]
  have hinv := coverPrtFun_involutive (mV Φ) (permL Φ 0) (permL Φ 1)
  simp only [parentDart_def]
  constructor
  · intro h w hw
    obtain ⟨h1, h2⟩ := h w hw
    exact ⟨fun he => h2 (by rw [he]), fun he => h1 (by rw [he, hinv])⟩
  · intro h w hw
    obtain ⟨h1, h2⟩ := h w hw
    refine ⟨fun he => h2 ?_, fun he => h1 ?_⟩
    · rw [← he, hinv]
    · exact hinv.injective he

end TreeDarts
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section FaceIndex

open Function MulAction

variable (hΦs : Φ ≤ sanovSubgroup)

noncomputable def orbU (i : Fin 3) (v : VΦ Φ) : OrbitU Φ i := Quotient.mk _ (β2 Φ (gOf i • v))

omit [Φ.FiniteIndex] in
theorem orbU_vOf (i : Fin 3) (O : OrbitU Φ i) : orbU Φ i (vOf Φ hΦs i O) = O := by
  rw [orbU, ← mk_pOf]
  exact mk_pOf_vOf Φ hΦs i O

omit [Φ.FiniteIndex] in
theorem orbU_faceGen_smul (i : Fin 3) (v : VΦ Φ) : orbU Φ i (faceGen i • v) = orbU Φ i v := by
  rw [orbU, orbU, ← U_smul_β2]
  apply Quotient.sound
  show (orbitRel (Subgroup.zpowers (U i)) _) (U i • β2 Φ (gOf i • v)) (β2 Φ (gOf i • v))
  rw [orbitRel_apply]
  exact mem_orbit _ (⟨U i, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers (U i))

omit [Φ.FiniteIndex] in
theorem orbU_pow_smul (i : Fin 3) (v : VΦ Φ) (r : ℕ) : orbU Φ i (faceGen i ^ r • v) = orbU Φ i v := by
  induction r with
  | zero => rw [pow_zero, one_smul]
  | succ r ih => rw [pow_succ', mul_smul, orbU_faceGen_smul, ih]

theorem exists_pow_smul_eq_zpow_smul {G X : Type*} [Group G] [MulAction G X] [Finite X] (a : G) (x : X) (z : ℤ) :
    ∃ n : ℕ, a ^ z • x = a ^ n • x := by
  have hper : 0 < minimalPeriod (a • ·) x := by
    refine minimalPeriod_pos_of_mem_periodicPts ⟨orderOf (MulAction.toPerm a : Equiv.Perm X), orderOf_pos _, ?_⟩
    have h : (MulAction.toPerm a : Equiv.Perm X) ^ orderOf (MulAction.toPerm a : Equiv.Perm X) = 1 := pow_orderOf_eq_one _
    have h' := congrArg (fun σ : Equiv.Perm X => σ x) h
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.coe_pow] at h'
    exact h'
  refine ⟨(z % (minimalPeriod (a • ·) x : ℤ)).toNat, ?_⟩
  rw [← zpow_smul_mod_minimalPeriod, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hper.ne'))]

theorem exists_pow_of_orbU_eq (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) {v v' : VΦ Φ} (h : orbU Φ i v = orbU Φ i v') :
    ∃ r : ℕ, v = faceGen i ^ r • v' := by
  have h1 : β2 Φ (gOf i • v) ∈ orbit (Subgroup.zpowers (U i)) (β2 Φ (gOf i • v')) := by
    rw [← orbitRel_apply]; exact Quotient.exact h
  obtain ⟨⟨g, hg⟩, hgx⟩ := h1
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zpow_smul (U i) (β2 Φ (gOf i • v')) z
  have hgx' : U i ^ n • β2 Φ (gOf i • v') = β2 Φ (gOf i • v) := by rw [← hn]; exact hgx
  refine ⟨n, smul_left_cancel (gOf i) (β2_injective Φ hΦs ?_)⟩
  rw [← hgx']
  clear hgx hgx' hn
  induction n with
  | zero => rw [pow_zero, one_smul, pow_zero, one_smul]
  | succ n ih => rw [pow_succ', mul_smul, ih, U_smul_β2, pow_succ' (faceGen i) n, mul_smul]

theorem exists_pow_vOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (w : VΦ Φ) :
    ∃ r : ℕ, w = faceGen i ^ r • vOf Φ hΦs i (orbU Φ i w) :=
  exists_pow_of_orbU_eq Φ hΦs i (by rw [orbU_vOf])

theorem exists_face (hΦs : Φ ≤ sanovSubgroup) (d : CD Φ) :
    ∃ (i : Fin 3) (O : OrbitU Φ i) (r : ℕ), ((G0 Φ).facePerm^[r]) (sdart Φ i (vOf Φ hΦs i O)) = cdU Φ d := by
  obtain ⟨j, s⟩ := d
  obtain ⟨w, rfl⟩ := (eV Φ).surjective j
  fin_cases s
  · obtain ⟨r, hr⟩ := exists_pow_vOf Φ hΦs 0 w
    refine ⟨0, orbU Φ 0 w, r, ?_⟩
    rw [sdart_zero, fp_iter_slot0]
    show cdU Φ (eV Φ (sanovBasis 0 ^ r • vOf Φ hΦs 0 (orbU Φ 0 w)), 0) = cdU Φ (eV Φ w, 0)
    rw [← faceGen_zero, ← hr]
  ·
    obtain ⟨r, hr⟩ := exists_pow_vOf Φ hΦs 2 ((sanL 1)⁻¹ • w)
    refine ⟨2, orbU Φ 2 ((sanL 1)⁻¹ • w), 2 * r + 1, ?_⟩
    rw [sdart_two, fp_iter_slot3_odd, ← hr, smul_inv_smul]
    rfl
  · obtain ⟨r, hr⟩ := exists_pow_vOf Φ hΦs 1 w
    refine ⟨1, orbU Φ 1 w, r, ?_⟩
    rw [sdart_one, fp_iter_slot2]
    show cdU Φ (eV Φ ((sanovBasis 1)⁻¹ ^ r • vOf Φ hΦs 1 (orbU Φ 1 w)), 2) = cdU Φ (eV Φ w, 2)
    rw [← faceGen_one, ← hr]
  · obtain ⟨r, hr⟩ := exists_pow_vOf Φ hΦs 2 w
    refine ⟨2, orbU Φ 2 w, 2 * r, ?_⟩
    rw [sdart_two, fp_iter_slot3_even, ← hr]
    rfl

theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp

theorem dseq0_eq (v : VΦ Φ) (r : ℕ) : dseq Φ 0 v r = (eV Φ (faceGen 0 ^ r • v), 0) := by
  rw [dseq, sdart_zero, fp_iter_slot0, cdU_val, faceGen_zero]
theorem dseq1_eq (v : VΦ Φ) (r : ℕ) : dseq Φ 1 v r = (eV Φ (faceGen 1 ^ r • v), 2) := by
  rw [dseq, sdart_one, fp_iter_slot2, cdU_val, faceGen_one]
theorem dseq2_even_eq (v : VΦ Φ) (k : ℕ) : dseq Φ 2 v (2 * k) = (eV Φ (faceGen 2 ^ k • v), 3) := by
  rw [dseq, sdart_two, fp_iter_slot3_even, cdU_val]
theorem dseq2_odd_eq (v : VΦ Φ) (k : ℕ) : dseq Φ 2 v (2 * k + 1) = (eV Φ (sanL 1 • faceGen 2 ^ k • v), 1) := by
  rw [dseq, sdart_two, fp_iter_slot3_odd, cdU_val]

theorem sdart0_val (v : VΦ Φ) : (sdart Φ 0 v : CD Φ) = (eV Φ v, 0) := rfl
theorem sdart1_val (v : VΦ Φ) : (sdart Φ 1 v : CD Φ) = (eV Φ v, 2) := rfl
theorem sdart2_val (v : VΦ Φ) : (sdart Φ 2 v : CD Φ) = (eV Φ v, 3) := rfl

theorem type_eq_of_dseq_eq_sdart (i i' : Fin 3) (v v' : VΦ Φ) (r : ℕ) (h : dseq Φ i v r = (sdart Φ i' v' : CD Φ)) : i = i' := by
  have hs := congrArg Prod.snd h
  rcases fin_three_cases i with rfl | rfl | rfl <;> rcases fin_three_cases i' with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       first
       | (rw [dseq0_eq] at hs; simp [sdart1_val, sdart2_val] at hs)
       | (rw [dseq1_eq] at hs; simp [sdart0_val, sdart2_val] at hs)
       | (obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' r
          · rw [dseq2_even_eq] at hs; simp [sdart0_val, sdart1_val] at hs
          · rw [dseq2_odd_eq] at hs; simp [sdart0_val, sdart1_val] at hs))

theorem orbit_eq_of_dseq_eq_sdart (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O O' : OrbitU Φ i) (r : ℕ)
    (h : dseq Φ i (vOf Φ hΦs i O) r = (sdart Φ i (vOf Φ hΦs i O') : CD Φ)) : O = O' := by
  rw [← orbU_vOf Φ hΦs i O, ← orbU_vOf Φ hΦs i O']

  have key : ∀ k : ℕ, faceGen i ^ k • vOf Φ hΦs i O = vOf Φ hΦs i O' →
      orbU Φ i (vOf Φ hΦs i O) = orbU Φ i (vOf Φ hΦs i O') := fun k hk => by rw [← hk, orbU_pow_smul]
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [dseq0_eq, sdart0_val, Prod.mk.injEq] at h
    exact key r ((eV Φ).injective h.1)
  · rw [dseq1_eq, sdart1_val, Prod.mk.injEq] at h
    exact key r ((eV Φ).injective h.1)
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' r
    · rw [dseq2_even_eq, sdart2_val, Prod.mk.injEq] at h
      exact key k ((eV Φ).injective h.1)
    · rw [dseq2_odd_eq, sdart2_val, Prod.mk.injEq] at h
      exact absurd h.2 (by decide)

end FaceIndex
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section Transfer

open Function MulAction Equiv.Perm PDPairing.Chord

variable {n : ℕ} (Dg : ChordDiagram n)

noncomputable def rep (q : Fin (2 * n)) : Fin (2 * n) := (Dg.orbitFinset q).min' ⟨q, Dg.mem_orbitFinset_self q⟩

theorem rep_mem_orbitFinset (q : Fin (2 * n)) : rep Dg q ∈ Dg.orbitFinset q := Finset.min'_mem _ _

theorem orbitFinset_rep (q : Fin (2 * n)) : Dg.orbitFinset (rep Dg q) = Dg.orbitFinset q :=
  Dg.orbitFinset_eq_of_mem (rep_mem_orbitFinset Dg q)

theorem rep_mem_faceReps (q : Fin (2 * n)) : rep Dg q ∈ Dg.faceReps := by
  rw [ChordDiagram.faceReps, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun q' hq' => ?_⟩
  rw [orbitFinset_rep] at hq'
  exact Finset.min'_le _ _ hq'

theorem rep_eq_self_of_mem_faceReps {p : Fin (2 * n)} (hp : p ∈ Dg.faceReps) : rep Dg p = p := by
  rw [ChordDiagram.faceReps, Finset.mem_filter] at hp
  exact le_antisymm (Finset.min'_le _ _ (Dg.mem_orbitFinset_self p)) (hp.2 _ (rep_mem_orbitFinset Dg p))

theorem rep_eq_rep_of_orbitFinset_eq {q q' : Fin (2 * n)} (h : Dg.orbitFinset q = Dg.orbitFinset q') :
    rep Dg q = rep Dg q' := by
  unfold rep
  congr 1

theorem orbitFinset_eq_of_rep_eq {q q' : Fin (2 * n)} (h : rep Dg q = rep Dg q') : Dg.orbitFinset q = Dg.orbitFinset q' := by
  rw [← orbitFinset_rep Dg q, ← orbitFinset_rep Dg q', h]

theorem mem_orbitFinset_iff_sameCycle (q q' : Fin (2 * n)) : q' ∈ Dg.orbitFinset q ↔ SameCycle Dg.facePerm q q' := by
  constructor
  · intro h
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨k, by rw [zpow_natCast]⟩
  · intro h
    obtain ⟨k, -, hk⟩ := h.exists_pow_eq'
    rw [← hk]
    have hper := Dg.mem_periodicPts_facePerm q
    refine Finset.mem_image.mpr ⟨k % minimalPeriod Dg.facePerm q, Finset.mem_range.mpr
      (Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hper)), ?_⟩
    rw [ChordDiagram.perm_pow_apply, ChordDiagram.perm_pow_apply, iterate_mod_minimalPeriod_eq]

theorem orbitFinset_eq_iff_sameCycle (q q' : Fin (2 * n)) :
    Dg.orbitFinset q = Dg.orbitFinset q' ↔ SameCycle Dg.facePerm q q' := by
  rw [← mem_orbitFinset_iff_sameCycle, Dg.mem_orbitFinset_iff, eq_comm]

structure GlueData where
  t : Finset (CD Φ)
  H : Fatgraph t
  C : ContractionSeq Finset.univ (G0 Φ) t H
  hprt : ∀ x : ↥t, ((H.prt x : ↥t) : CD Φ) = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) ↑x
  hmem : ∀ d : CD Φ, d ∈ t ↔ ∀ (w : Fin (mV Φ)) (hw : w ≠ (treeDataOf Φ).v₀),
    d ≠ (treeDataOf Φ).childDart w hw ∧ d ≠ (treeDataOf Φ).parentDart w hw
  hone : ∀ d f : ↥t, H.SameVertex d f
  nc : ℕ
  Dg : ChordDiagram nc
  φc : ↥t ≃ Fin (2 * nc)
  hrot : ∀ d, φc (H.rot d) = finRotate (2 * nc) (φc d)
  hpart : ∀ d, φc (H.prt d) = Dg.partner (φc d)

variable {Φ}
variable (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ)

theorem exists_iter_mem (x : ↥(Finset.univ : Finset (CD Φ))) :
    ∃ k : ℕ, ((((G0 Φ).facePerm ^ k) x : ↥(Finset.univ : Finset (CD Φ))) : CD Φ) ∈ X.t :=
  (treeDataOf Φ).face_meets X.t X.hmem x

noncomputable def kOf (i : Fin 3) (O : OrbitU Φ i) : ℕ := Classical.choose (exists_iter_mem X (sdart Φ i (vOf Φ hΦs i O)))

theorem kOf_spec (i : Fin 3) (O : OrbitU Φ i) :
    ((((G0 Φ).facePerm ^ kOf hΦs X i O) (sdart Φ i (vOf Φ hΦs i O)) : ↥(Finset.univ : Finset (CD Φ))) : CD Φ) ∈ X.t :=
  Classical.choose_spec (exists_iter_mem X (sdart Φ i (vOf Φ hΦs i O)))

noncomputable def yOf (i : Fin 3) (O : OrbitU Φ i) : ↥X.t := ⟨_, kOf_spec hΦs X i O⟩

theorem cdU_yOf (i : Fin 3) (O : OrbitU Φ i) :
    cdU Φ ((yOf hΦs X i O : ↥X.t) : CD Φ) = ((G0 Φ).facePerm ^ kOf hΦs X i O) (sdart Φ i (vOf Φ hΦs i O)) :=
  Subtype.ext rfl

noncomputable def Θ (x : Σ i : Fin 3, OrbitU Φ i) : Fin (2 * X.nc) := rep X.Dg (X.φc (yOf hΦs X x.1 x.2))

theorem Θ_mem (x : Σ i : Fin 3, OrbitU Φ i) : Θ hΦs X x ∈ X.Dg.faceReps := rep_mem_faceReps X.Dg _

theorem sameCycle_chord_iff_cover (y y' : ↥X.t) :
    SameCycle X.Dg.facePerm (X.φc y) (X.φc y') ↔ SameCycle (G0 Φ).facePerm (cdU Φ (y : CD Φ)) (cdU Φ (y' : CD Φ)) := by
  rw [show X.Dg.facePerm = X.Dg.partner.trans (finRotate (2 * X.nc)) from rfl,
    X.H.chordFace_sameCycle_iff X.Dg X.φc X.hrot X.hpart, Fatgraph.pipe_sameCycle_iff X.C y y' (Finset.mem_univ _) (Finset.mem_univ _)]
  rfl

theorem Θ_injective : Injective (Θ hΦs X) := by
  rintro ⟨i, O⟩ ⟨i', O'⟩ h
  have hcyc : SameCycle (G0 Φ).facePerm (sdart Φ i (vOf Φ hΦs i O)) (sdart Φ i' (vOf Φ hΦs i' O')) := by
    have h1 := (orbitFinset_eq_iff_sameCycle X.Dg _ _).mp (orbitFinset_eq_of_rep_eq X.Dg h)
    rw [sameCycle_chord_iff_cover, cdU_yOf, cdU_yOf] at h1
    exact (sameCycle_pow_left.mp (sameCycle_pow_left.mp h1).symm).symm
  obtain ⟨r, -, hr⟩ := hcyc.exists_pow_eq'
  have hr' : dseq Φ i (vOf Φ hΦs i O) r = (sdart Φ i' (vOf Φ hΦs i' O') : CD Φ) := by
    rw [dseq, ← Equiv.Perm.coe_pow]; exact congrArg Subtype.val hr
  obtain rfl := type_eq_of_dseq_eq_sdart Φ i i' _ _ r hr'
  obtain rfl := orbit_eq_of_dseq_eq_sdart Φ hΦs i O O' r hr'
  rfl

theorem Θ_surjOn (p : Fin (2 * X.nc)) (hp : p ∈ X.Dg.faceReps) : ∃ x, Θ hΦs X x = p := by
  obtain ⟨i, O, r, hr⟩ := exists_face Φ hΦs ((X.φc.symm p : ↥X.t) : CD Φ)
  refine ⟨⟨i, O⟩, ?_⟩
  rw [← rep_eq_self_of_mem_faceReps X.Dg hp]
  apply rep_eq_rep_of_orbitFinset_eq
  rw [orbitFinset_eq_iff_sameCycle]
  conv_rhs => rw [← X.φc.apply_symm_apply p]
  rw [sameCycle_chord_iff_cover, cdU_yOf, ← hr, ← Equiv.Perm.coe_pow]
  exact (sameCycle_pow_left.mpr (sameCycle_pow_left.mpr (SameCycle.refl _ _)).symm).symm

noncomputable def ΘEquiv : (Σ i : Fin 3, OrbitU Φ i) ≃ ↥X.Dg.faceReps :=
  Equiv.ofBijective (fun x => ⟨Θ hΦs X x, Θ_mem hΦs X x⟩)
    ⟨fun x x' h => Θ_injective hΦs X (congrArg Subtype.val h),
     fun ⟨p, hp⟩ => by
      obtain ⟨x, hx⟩ := Θ_surjOn hΦs X p hp
      exact ⟨x, Subtype.ext hx⟩⟩

theorem ΘEquiv_val (x : Σ i : Fin 3, OrbitU Φ i) : ((ΘEquiv hΦs X x : ↥X.Dg.faceReps) : Fin (2 * X.nc)) = Θ hΦs X x := rfl

variable (Φ) in

theorem nonempty_glueData : Nonempty (GlueData Φ) := by
  obtain ⟨t, H, C, hcard, hprt, hmem, hone⟩ := (treeDataOf Φ).exists_contraction (mV_pos Φ)
  obtain ⟨Dg, φc, hrot, hpart⟩ := Fatgraph.exists_chordDiagram H (mV Φ + 1) (Nat.succ_pos _) hcard hone
  exact ⟨⟨t, H, C, hprt, hmem, hone, mV Φ + 1, Dg, φc, hrot, hpart⟩⟩

section T2

variable {M : Type*} [AddCommMonoid M] {R' : Type*} [CommRing R']

noncomputable def cSum (g : CD Φ → M) (x : ↥(Finset.univ : Finset (CD Φ))) : M :=
  ∑ r ∈ Finset.range (minimalPeriod (⇑(G0 Φ).facePerm) x), g ((((G0 Φ).facePerm)^[r]) x : CD Φ)

noncomputable def dSum (g : CD Φ → M) (q : Fin (2 * X.nc)) : M :=
  ∑ k ∈ Finset.range (minimalPeriod (⇑X.Dg.facePerm) q), g ((X.φc.symm ((⇑X.Dg.facePerm)^[k] q) : ↥X.t) : CD Φ)

noncomputable def cPair (f g : CD Φ → R') (x : ↥(Finset.univ : Finset (CD Φ))) : R' :=
  ∑ b ∈ Finset.range (minimalPeriod (⇑(G0 Φ).facePerm) x), ∑ a ∈ Finset.range b,
    (f ((((G0 Φ).facePerm)^[a]) x : CD Φ) * g ((((G0 Φ).facePerm)^[b]) x : CD Φ) -
      g ((((G0 Φ).facePerm)^[a]) x : CD Φ) * f ((((G0 Φ).facePerm)^[b]) x : CD Φ))

noncomputable def dPair (f g : CD Φ → R') (q : Fin (2 * X.nc)) : R' :=
  ∑ b ∈ Finset.range (minimalPeriod (⇑X.Dg.facePerm) q), ∑ a ∈ Finset.range b,
    (f ((X.φc.symm ((⇑X.Dg.facePerm)^[a] q) : ↥X.t) : CD Φ) * g ((X.φc.symm ((⇑X.Dg.facePerm)^[b] q) : ↥X.t) : CD Φ) -
      g ((X.φc.symm ((⇑X.Dg.facePerm)^[a] q) : ↥X.t) : CD Φ) * f ((X.φc.symm ((⇑X.Dg.facePerm)^[b] q) : ↥X.t) : CD Φ))

theorem cSum_shift (g : CD Φ → M) (x : ↥(Finset.univ : Finset (CD Φ))) (s : ℕ) :
    cSum g ((((G0 Φ).facePerm)^[s]) x) = cSum g x := by
  unfold cSum
  exact orbitSum_iterate _ (fun z : ↥(Finset.univ : Finset (CD Φ)) => g (z : CD Φ)) x (mem_periodicPts_fp Φ x) s

theorem dSum_shift (g : CD Φ → M) (q : Fin (2 * X.nc)) (s : ℕ) :
    dSum X g ((⇑X.Dg.facePerm)^[s] q) = dSum X g q := by
  unfold dSum
  exact orbitSum_iterate _ (fun z => g ((X.φc.symm z : ↥X.t) : CD Φ)) q (X.Dg.mem_periodicPts_facePerm q) s

theorem dSum_rep (g : CD Φ → M) (q : Fin (2 * X.nc)) : dSum X g (rep X.Dg q) = dSum X g q := by
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (rep_mem_orbitFinset X.Dg q)
  rw [← hj, ChordDiagram.perm_pow_apply, dSum_shift]

theorem hSum_eq_dSum (g : CD Φ → M) (y : ↥X.t) :
    ∑ k ∈ Finset.range (minimalPeriod (⇑X.H.facePerm) y), g (((X.H.facePerm ^ k) y : ↥X.t) : CD Φ) = dSum X g (X.φc y) := by
  unfold dSum
  rw [show X.Dg.facePerm = X.Dg.partner.trans (finRotate (2 * X.nc)) from rfl,
    X.H.chordFace_minimalPeriod X.Dg X.φc X.hrot X.hpart y]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  apply X.φc.injective
  rw [Equiv.apply_symm_apply, ← Equiv.Perm.coe_pow, X.H.chordFace_equivariant_pow X.Dg X.φc X.hrot X.hpart k y]

theorem cSum_sdart_eq_dSum_Θ (g : CD Φ → M) (hg : ∀ d, d ∉ X.t → g d = 0) (i : Fin 3) (O : OrbitU Φ i) :
    cSum g (sdart Φ i (vOf Φ hΦs i O)) = dSum X g (Θ hΦs X ⟨i, O⟩) := by
  show cSum g (sdart Φ i (vOf Φ hΦs i O)) = dSum X g (rep X.Dg (X.φc (yOf hΦs X i O)))
  rw [dSum_rep, ← hSum_eq_dSum, ← cSum_shift g _ (kOf hΦs X i O), ← Equiv.Perm.coe_pow, ← cdU_yOf]
  unfold cSum
  have h := Fatgraph.pipe_orbit_sum_gen (G0 Φ) X.C g (fun d _ hd => hg d hd) (yOf hΦs X i O)
  simp only [Equiv.Perm.coe_pow] at h ⊢
  convert h.symm using 2
  rfl
  rfl

theorem cPair_shift (f g : CD Φ → R') (x : ↥(Finset.univ : Finset (CD Φ))) (hf : cSum f x = 0)
    (hg : cSum g x = 0) (s : ℕ) :
    cPair f g ((((G0 Φ).facePerm)^[s]) x) = cPair f g x := by
  unfold cPair
  exact pairOrbitSum_iterate _ (fun z : ↥(Finset.univ : Finset (CD Φ)) => f (z : CD Φ)) (fun z => g (z : CD Φ)) x
    (mem_periodicPts_fp Φ x) hf hg s

theorem dPair_shift (f g : CD Φ → R') (q : Fin (2 * X.nc)) (hf : dSum X f q = 0) (hg : dSum X g q = 0) (s : ℕ) :
    dPair X f g ((⇑X.Dg.facePerm)^[s] q) = dPair X f g q := by
  unfold dPair
  exact pairOrbitSum_iterate _ (fun z => f ((X.φc.symm z : ↥X.t) : CD Φ)) (fun z => g ((X.φc.symm z : ↥X.t) : CD Φ)) q
    (X.Dg.mem_periodicPts_facePerm q) hf hg s

theorem dPair_rep (f g : CD Φ → R') (q : Fin (2 * X.nc)) (hf : dSum X f q = 0) (hg : dSum X g q = 0) :
    dPair X f g (rep X.Dg q) = dPair X f g q := by
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (rep_mem_orbitFinset X.Dg q)
  rw [← hj, ChordDiagram.perm_pow_apply, dPair_shift X f g q hf hg]

theorem hPair_eq_dPair (f g : CD Φ → R') (y : ↥X.t) :
    ∑ b ∈ Finset.range (minimalPeriod (⇑X.H.facePerm) y), ∑ a ∈ Finset.range b,
      (f (((X.H.facePerm ^ a) y : ↥X.t) : CD Φ) * g (((X.H.facePerm ^ b) y : ↥X.t) : CD Φ) -
        g (((X.H.facePerm ^ a) y : ↥X.t) : CD Φ) * f (((X.H.facePerm ^ b) y : ↥X.t) : CD Φ)) = dPair X f g (X.φc y) := by
  unfold dPair
  rw [show X.Dg.facePerm = X.Dg.partner.trans (finRotate (2 * X.nc)) from rfl,
    X.H.chordFace_minimalPeriod X.Dg X.φc X.hrot X.hpart y]
  have hk : ∀ k, ((X.H.facePerm ^ k) y : ↥X.t) = X.φc.symm ((⇑(X.Dg.partner.trans (finRotate (2 * X.nc))))^[k] (X.φc y)) := by
    intro k
    apply X.φc.injective
    rw [Equiv.apply_symm_apply, ← Equiv.Perm.coe_pow, X.H.chordFace_equivariant_pow X.Dg X.φc X.hrot X.hpart k y]
  simp_rw [hk]

theorem cPair_sdart_eq_dPair_Θ (f g : CD Φ → R') (hf0 : ∀ d, d ∉ X.t → f d = 0) (hg0 : ∀ d, d ∉ X.t → g d = 0)
    (i : Fin 3) (O : OrbitU Φ i) (hf : cSum f (sdart Φ i (vOf Φ hΦs i O)) = 0)
    (hg : cSum g (sdart Φ i (vOf Φ hΦs i O)) = 0) :
    cPair f g (sdart Φ i (vOf Φ hΦs i O)) = dPair X f g (Θ hΦs X ⟨i, O⟩) := by
  have hfq : dSum X f (X.φc (yOf hΦs X i O)) = 0 := by
    have h := cSum_sdart_eq_dSum_Θ hΦs X f hf0 i O
    rw [hf] at h
    exact (dSum_rep X f _).symm.trans h.symm
  have hgq : dSum X g (X.φc (yOf hΦs X i O)) = 0 := by
    have h := cSum_sdart_eq_dSum_Θ hΦs X g hg0 i O
    rw [hg] at h
    exact (dSum_rep X g _).symm.trans h.symm
  show cPair f g (sdart Φ i (vOf Φ hΦs i O)) = dPair X f g (rep X.Dg (X.φc (yOf hΦs X i O)))
  rw [dPair_rep X f g _ hfq hgq, ← hPair_eq_dPair, ← cPair_shift f g _ hf hg (kOf hΦs X i O),
    ← Equiv.Perm.coe_pow, ← cdU_yOf]
  unfold cPair
  have h := Fatgraph.pipe_orbit_pairSum (G0 Φ) X.C (fun d d' => f d * g d' - g d * f d')
    (fun d _ hd => ⟨fun d' => by show f d * g d' - g d * f d' = 0; rw [hf0 d hd, hg0 d hd, zero_mul, zero_mul, sub_zero],
      fun d' => by show f d' * g d - g d' * f d = 0; rw [hf0 d hd, hg0 d hd, mul_zero, mul_zero, sub_zero]⟩) (yOf hΦs X i O)
  simp only [Equiv.Perm.coe_pow] at h ⊢
  convert h.symm using 2
  rfl
  rfl

end T2
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section G2

variable {R : Type*} [CommRing R]

theorem dval_eq_zero_of_notMem (c : VΦ Φ → Fin 2 → R) (hc : c ∈ treeKer (R := R) Φ) (d : CD Φ) (hd : d ∉ X.t) :
    dval Φ c d = 0 := by
  obtain ⟨j, sl⟩ := d
  obtain ⟨w, rfl⟩ := (eV Φ).surjective j
  have key : ∀ (u : VΦ Φ) (i : Fin 2), fdart Φ u i ∉ X.t → c u i = 0 :=
    fun u i hu => hc u i ((fdart_notMem_iff Φ X.hmem u i).mp hu)
  fin_cases sl
  · exact (dval_slot0 Φ c w).trans (key w 0 hd)
  · replace hd : (eV Φ w, (1 : Fin 4)) ∉ X.t := hd
    show dval Φ c (eV Φ w, 1) = 0
    rw [dval_slot1, key _ 0 ?_, neg_zero]
    rw [← prt_mem_iff Φ X.hmem] at hd
    rwa [show fdart Φ ((sanL 0)⁻¹ • w) 0 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 1) by
      rw [fdart, ← permL_symm_eV]; rfl]
  · replace hd : (eV Φ w, (2 : Fin 4)) ∉ X.t := hd
    show dval Φ c (eV Φ w, 2) = 0
    rw [dval_slot2, key _ 1 ?_, neg_zero]
    rw [← prt_mem_iff Φ X.hmem] at hd
    rwa [show fdart Φ ((sanL 1)⁻¹ • w) 1 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 2) by
      rw [fdart, ← permL_symm_eV]; rfl]
  · exact (dval_slot3 Φ c w).trans (key w 1 hd)

theorem hD_eq_zero_of_notMem (h : Φ → R)
    (htree : ∀ (w : VΦ Φ) (i : Fin 2), (treeT Φ).tree w i = true → h (stabEquiv Φ hΦs ((treeT Φ).sx w (i, true))) = 0)
    (hodd : ∀ (w : VΦ Φ) (i : Fin 2), h (stabEquiv Φ hΦs ((treeT Φ).sx w (i, false))) =
      -h (stabEquiv Φ hΦs ((treeT Φ).sx ((sanL i)⁻¹ • w) (i, true))))
    (d : CD Φ) (hd : d ∉ X.t) : hD Φ hΦs h d = 0 := by
  obtain ⟨j, sl⟩ := d
  obtain ⟨w, rfl⟩ := (eV Φ).surjective j
  have key : ∀ (u : VΦ Φ) (i : Fin 2), fdart Φ u i ∉ X.t → h (stabEquiv Φ hΦs ((treeT Φ).sx u (i, true))) = 0 :=
    fun u i hu => htree u i ((fdart_notMem_iff Φ X.hmem u i).mp hu)
  fin_cases sl
  · exact (hD_slot0 Φ hΦs h w).trans (key w 0 hd)
  · replace hd : (eV Φ w, (1 : Fin 4)) ∉ X.t := hd
    show hD Φ hΦs h (eV Φ w, 1) = 0
    rw [hD_slot1, hodd, key _ 0 ?_, neg_zero]
    rw [← prt_mem_iff Φ X.hmem] at hd
    rwa [show fdart Φ ((sanL 0)⁻¹ • w) 0 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 1) by
      rw [fdart, ← permL_symm_eV]; rfl]
  · replace hd : (eV Φ w, (2 : Fin 4)) ∉ X.t := hd
    show hD Φ hΦs h (eV Φ w, 2) = 0
    rw [hD_slot2, hodd, key _ 1 ?_, neg_zero]
    rw [← prt_mem_iff Φ X.hmem] at hd
    rwa [show fdart Φ ((sanL 1)⁻¹ • w) 1 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 2) by
      rw [fdart, ← permL_symm_eV]; rfl]
  · exact (hD_slot3 Φ hΦs h w).trans (key w 1 hd)

theorem cSum_dval_sdart (c : VΦ Φ → Fin 2 → R) (i : Fin 3) (v : VΦ Φ) :
    cSum (dval Φ c) (sdart Φ i v) = walkSum Φ c v (faceWord i (faceLen Φ i v)) := by
  unfold cSum
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [walkSum_faceWord_eq_CS0, CS, sdart_zero, minimalPeriod_slot0]; rfl
  · rw [walkSum_faceWord_eq_CS1, CS, sdart_one, minimalPeriod_slot2]; rfl
  · rw [walkSum_faceWord_eq_CS2, CS, sdart_two, minimalPeriod_slot3]; rfl

variable {M : Type*} [AddCommMonoid M] in
theorem cSum_hD_sdart (h : Φ → M) (i : Fin 3) (v : VΦ Φ) :
    cSum (hD Φ hΦs h) (sdart Φ i v) = ((letters Φ hΦs v (faceWord i (faceLen Φ i v))).map h).sum := by
  unfold cSum
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [sum_letters_faceWord0, sdart_zero, minimalPeriod_slot0]; rfl
  · rw [sum_letters_faceWord1, sdart_one, minimalPeriod_slot2]; rfl
  · rw [sum_letters_faceWord2, sdart_two, minimalPeriod_slot3]; rfl

theorem cPair_dval_sdart [IsFreeGroup Φ] (φ ψ : Additive Φ →+ R) (i : Fin 3) (v : VΦ Φ) :
    cPair (dval Φ (edgeVal Φ hΦs φ)) (dval Φ (edgeVal Φ hΦs ψ)) (sdart Φ i v) =
      - pairSum φ ψ (letters Φ hΦs v (faceWord i (faceLen Φ i v))) := by
  unfold cPair
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [pairSum_letters_faceWord0, neg_neg, CP, sdart_zero, minimalPeriod_slot0]; rfl
  · rw [pairSum_letters_faceWord1, neg_neg, CP, sdart_one, minimalPeriod_slot2]; rfl
  · rw [pairSum_letters_faceWord2, neg_neg, CP, sdart_two, minimalPeriod_slot3]; rfl

noncomputable def prtEquiv : Equiv.Perm (CD Φ) :=
  (coverPrtFun_involutive (mV Φ) (permL Φ 0) (permL Φ 1)).toPerm _

theorem sum_odd_eq_zero [Invertible (2 : R)] (F : CD Φ → R)
    (hF : ∀ d, F (coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d) = -F d) : ∑ d : CD Φ, F d = 0 := by
  have h : ∑ d : CD Φ, F d = -∑ d : CD Φ, F d := by
    conv_lhs => rw [← Equiv.sum_comp (prtEquiv (Φ := Φ)) F]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => hF d
  have h2 : (2 : R) * ∑ d : CD Φ, F d = 0 := by rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel _
  calc ∑ d : CD Φ, F d = ⅟(2 : R) * ((2 : R) * ∑ d : CD Φ, F d) := by rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h2, mul_zero]

noncomputable def GOf (c : VΦ Φ → Fin 2 → R) : Fin X.nc → R := fun j => dval Φ c ((X.φc.symm (X.Dg.pos j) : ↥X.t) : CD Φ)

theorem GOf_add (c c' : VΦ Φ → Fin 2 → R) : GOf X (c + c') = GOf X c + GOf X c' := by
  funext j; exact dval_add Φ c c' _

theorem GOf_smul (r : R) (c : VΦ Φ → Fin 2 → R) : GOf X (r • c) = r • GOf X c := by
  funext j; exact dval_smul Φ r c _

theorem φc_symm_partner (q : Fin (2 * X.nc)) : X.φc.symm (X.Dg.partner q) = X.H.prt (X.φc.symm q) := by
  apply X.φc.injective
  rw [Equiv.apply_symm_apply, X.hpart, Equiv.apply_symm_apply]

theorem letterAtR_GOf (c : VΦ Φ → Fin 2 → R) (q : Fin (2 * X.nc)) :
    X.Dg.letterAtR (GOf X c) q = dval Φ c ((X.φc.symm q : ↥X.t) : CD Φ) := by
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := X.Dg.pos_or_neg q
  · rw [ChordDiagram.letterAtR_pos]; rfl
  · rw [ChordDiagram.letterAtR_neg, ← ChordDiagram.partner_pos, φc_symm_partner, X.hprt, dval_prt]
    rfl

theorem dSum_dval_eq_faceSumR (c : VΦ Φ → Fin 2 → R) (q : Fin (2 * X.nc)) :
    dSum X (dval Φ c) q = X.Dg.faceSumR (GOf X c) q := by
  unfold dSum ChordDiagram.faceSumR
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [letterAtR_GOf, ChordDiagram.perm_pow_apply]

theorem dPair_dval_eq_neg_HfaceR (c c' : VΦ Φ → Fin 2 → R) (q : Fin (2 * X.nc)) :
    dPair X (dval Φ c) (dval Φ c') q = - X.Dg.HfaceR q (GOf X c) (GOf X c') := by
  unfold dPair ChordDiagram.HfaceR
  rw [neg_neg]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [letterAtR_GOf, letterAtR_GOf, letterAtR_GOf, letterAtR_GOf, ChordDiagram.perm_pow_apply, ChordDiagram.perm_pow_apply]

theorem faceTerm_eq [IsFreeGroup Φ] [Invertible (2 : R)] (φ ψ : Additive Φ →+ R) (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ)
    (i : Fin 3) (O : OrbitU Φ i) :
    ((letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))).map (hPrim φ ψ)).sum -
        pairSum φ ψ (letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))) =
      dSum X (hD Φ hΦs (hPrim φ ψ)) (Θ hΦs X ⟨i, O⟩) +
        dPair X (dval Φ (edgeVal Φ hΦs φ)) (dval Φ (edgeVal Φ hΦs ψ)) (Θ hΦs X ⟨i, O⟩) := by
  have hvan : ∀ χ : Additive Φ →+ R, ∀ d, d ∉ X.t → dval Φ (edgeVal Φ hΦs χ) d = 0 :=
    fun χ d hd => dval_eq_zero_of_notMem X _ (fun v i h => edgeVal_tree Φ hΦs χ v i h) d hd
  have hsing : ∀ χ : Additive Φ →+ R, IsPar Φ χ → cSum (dval Φ (edgeVal Φ hΦs χ)) (sdart Φ i (vOf Φ hΦs i O)) = 0 :=
    fun χ hχ => by rw [cSum_dval_sdart]; exact (isPar_iff_walkSum Φ hΦs χ).mp hχ i _
  rw [sub_eq_add_neg, ← cSum_hD_sdart, ← cPair_dval_sdart,
    cSum_sdart_eq_dSum_Θ hΦs X _ (hD_eq_zero_of_notMem hΦs X (hPrim φ ψ)
      (fun w i h => hPrim_letter_tree Φ hΦs φ ψ w i h) (fun w i => hPrim_letter_false Φ hΦs φ ψ w i)),
    cPair_sdart_eq_dPair_Θ hΦs X _ _ (hvan φ) (hvan ψ) i O (hsing φ hφ) (hsing ψ hψ)]

theorem pairF_eq_neg_faceFormR [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (φ ψ : Additive Φ →+ R)
    (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ) :
    pairF Φ φ ψ = - X.Dg.faceFormR (GOf X (edgeVal Φ hΦs φ)) (GOf X (edgeVal Φ hΦs ψ)) := by
  rw [pairF_eq_sum_letters Φ hΦs φ ψ hφ hψ]

  have h1 : (∑ i : Fin 3, ∑ O : OrbitU Φ i,
      ((((letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))).map (hPrim φ ψ)).sum -
        pairSum φ ψ (letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O))))))) =
      ∑ p ∈ X.Dg.faceReps, (dSum X (hD Φ hΦs (hPrim φ ψ)) p +
        dPair X (dval Φ (edgeVal Φ hΦs φ)) (dval Φ (edgeVal Φ hΦs ψ)) p) := by
    rw [← Finset.sum_coe_sort X.Dg.faceReps, ← Fintype.sum_equiv (ΘEquiv hΦs X)
      (fun x : Σ i : Fin 3, OrbitU Φ i => dSum X (hD Φ hΦs (hPrim φ ψ)) (Θ hΦs X x) +
        dPair X (dval Φ (edgeVal Φ hΦs φ)) (dval Φ (edgeVal Φ hΦs ψ)) (Θ hΦs X x)) _ (fun x => rfl),
      ← Finset.univ_sigma_univ, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun O _ => faceTerm_eq hΦs X φ ψ hφ hψ i O
  rw [h1, Finset.sum_add_distrib]

  have h2 : ∑ p ∈ X.Dg.faceReps, dSum X (hD Φ hΦs (hPrim φ ψ)) p = 0 := by
    have hper := X.Dg.sum_faceReps_period_gen (fun q => hD Φ hΦs (hPrim φ ψ) ((X.φc.symm q : ↥X.t) : CD Φ))
    simp only [ChordDiagram.perm_pow_apply] at hper
    unfold dSum
    rw [hper, Equiv.sum_comp X.φc.symm (fun y : ↥X.t => hD Φ hΦs (hPrim φ ψ) (y : CD Φ)), Finset.sum_coe_sort,
      Finset.sum_subset (Finset.subset_univ X.t) (fun d _ hd => hD_eq_zero_of_notMem hΦs X (hPrim φ ψ)
        (fun w i h => hPrim_letter_tree Φ hΦs φ ψ w i h) (fun w i => hPrim_letter_false Φ hΦs φ ψ w i) d hd)]
    exact sum_odd_eq_zero _ (hD_prt Φ hΦs (hPrim φ ψ) (fun w i => hPrim_letter_false Φ hΦs φ ψ w i))
  rw [h2, zero_add, ChordDiagram.faceFormR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => dPair_dval_eq_neg_HfaceR X _ _ p

end G2
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section Alpha

variable {R : Type*} [CommRing R]

theorem sdart_pow_smul_eq_iter (i : Fin 3) (v : VΦ Φ) (r : ℕ) :
    ∃ s : ℕ, sdart Φ i (faceGen i ^ r • v) = ((G0 Φ).facePerm^[s]) (sdart Φ i v) := by
  rcases fin_three_cases i with rfl | rfl | rfl
  · refine ⟨r, ?_⟩
    rw [sdart_zero, sdart_zero, fp_iter_slot0, faceGen_zero]
  · refine ⟨r, ?_⟩
    rw [sdart_one, sdart_one, fp_iter_slot2, faceGen_one]
  · exact ⟨2 * r, by rw [sdart_two, sdart_two, fp_iter_slot3_even]⟩

variable {M : Type*} [AddCommMonoid M] in

theorem cSum_sdart_any (hΦs : Φ ≤ sanovSubgroup) (g : CD Φ → M) (i : Fin 3) (v : VΦ Φ) :
    cSum g (sdart Φ i v) = cSum g (sdart Φ i (vOf Φ hΦs i (orbU Φ i v))) := by
  obtain ⟨r, hr⟩ := exists_pow_vOf Φ hΦs i v
  obtain ⟨s, hs⟩ := sdart_pow_smul_eq_iter (Φ := Φ) i (vOf Φ hΦs i (orbU Φ i v)) r
  calc cSum g (sdart Φ i v) = cSum g (sdart Φ i (faceGen i ^ r • vOf Φ hΦs i (orbU Φ i v))) := by rw [← hr]
    _ = cSum g (((G0 Φ).facePerm^[s]) (sdart Φ i (vOf Φ hΦs i (orbU Φ i v)))) := by rw [hs]
    _ = _ := cSum_shift g _ s

theorem dSum_dval_eq_zero (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) (c : VΦ Φ → Fin 2 → R)
    (htree : c ∈ treeKer (R := R) Φ)
    (hwalk : ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ c v (faceWord i (faceLen Φ i v)) = 0) (q : Fin (2 * X.nc)) :
    dSum X (dval Φ c) q = 0 := by
  obtain ⟨⟨i, O⟩, hx⟩ := Θ_surjOn hΦs X (rep X.Dg q) (rep_mem_faceReps X.Dg q)
  rw [← dSum_rep, ← hx, ← cSum_sdart_eq_dSum_Θ hΦs X _ (dval_eq_zero_of_notMem X c htree), cSum_dval_sdart]
  exact hwalk _ _

theorem GOf_mem_faceKer (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) (c : VΦ Φ → Fin 2 → R)
    (hc : c ∈ parKer (R := R) Φ) : GOf X c ∈ X.Dg.faceKer (R := R) := by
  intro q
  rw [← dSum_dval_eq_faceSumR]
  exact dSum_dval_eq_zero hΦs X c hc.1 hc.2 q

section Inv2

variable [Invertible (2 : R)]

noncomputable def αFun (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) : ↥(parSub Φ R) →ₗ[R] X.Dg.faceKer (R := R) where
  toFun ψ := ⟨GOf X (edgeVal Φ hΦs (ψ : Additive Φ →+ R)), GOf_mem_faceKer hΦs X _ (parCoord Φ hΦs ψ).2⟩
  map_add' ψ ψ' := by
    apply Subtype.ext
    show GOf X (edgeVal Φ hΦs ((ψ : Additive Φ →+ R) + (ψ' : Additive Φ →+ R))) = GOf X _ + GOf X _
    rw [edgeVal_add, GOf_add]
  map_smul' r ψ := by
    apply Subtype.ext
    show GOf X (edgeVal Φ hΦs (r • (ψ : Additive Φ →+ R))) = r • GOf X _
    rw [edgeVal_smul, GOf_smul]

theorem αFun_coe (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) (ψ : ↥(parSub Φ R)) :
    ((αFun hΦs X ψ : X.Dg.faceKer (R := R)) : Fin X.nc → R) = GOf X (edgeVal Φ hΦs (ψ : Additive Φ →+ R)) :=
  rfl

omit [Invertible (2 : R)] in

theorem edgeFun_eq_zero (X : GlueData Φ) (c : VΦ Φ → Fin 2 → R) (htree : c ∈ treeKer (R := R) Φ)
    (hval : ∀ d, d ∈ X.t → dval Φ c d = 0) : c = 0 := by
  funext w i
  by_cases ht : (treeT Φ).tree w i = true
  · exact htree w i ht
  · have hmem : fdart Φ w i ∈ X.t := by
      by_contra h
      exact ht ((fdart_notMem_iff Φ X.hmem w i).mp h)
    have h := hval _ hmem
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · exact (dval_slot0 Φ c w).symm.trans h
    · exact (dval_slot3 Φ c w).symm.trans h

theorem αFun_injective (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) : Function.Injective (αFun hΦs X (R := R)) := by
  intro ψ ψ' h
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  set δ := ψ - ψ'
  have hG : GOf X (edgeVal Φ hΦs (δ : Additive Φ →+ R)) = 0 := congrArg Subtype.val h
  have hval : ∀ d, d ∈ X.t → dval Φ (edgeVal Φ hΦs (δ : Additive Φ →+ R)) d = 0 := by
    intro d hd
    have := letterAtR_GOf X (edgeVal Φ hΦs (δ : Additive Φ →+ R)) (X.φc ⟨d, hd⟩)
    rw [hG, Equiv.symm_apply_apply] at this
    rw [← this]
    unfold ChordDiagram.letterAtR
    simp
  have hc : edgeVal Φ hΦs (δ : Additive Φ →+ R) = 0 :=
    edgeFun_eq_zero X _ (fun v i ht => edgeVal_tree Φ hΦs _ v i ht) hval
  have hpc : parCoord Φ hΦs δ = 0 := Subtype.ext (by rw [parCoord_apply, hc]; rfl)
  exact (LinearEquiv.map_eq_zero_iff _).mp hpc

noncomputable def cOfG (X : GlueData Φ) (G : Fin X.nc → R) : VΦ Φ → Fin 2 → R := fun w i =>
  if h : fdart Φ w i ∈ X.t then X.Dg.letterAtR G (X.φc ⟨fdart Φ w i, h⟩) else 0

omit [Invertible (2 : R)] in
theorem cOfG_tree (X : GlueData Φ) (G : Fin X.nc → R) (w : VΦ Φ) (i : Fin 2) (ht : (treeT Φ).tree w i = true) :
    cOfG X G w i = 0 := by
  unfold cOfG
  rw [dif_neg ((fdart_notMem_iff Φ X.hmem w i).mpr ht)]

theorem prt_mk (X : GlueData Φ) (d : CD Φ) (hd : d ∈ X.t) :
    X.H.prt ⟨d, hd⟩ = ⟨coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d, (prt_mem_iff Φ X.hmem d).mpr hd⟩ :=
  Subtype.ext (X.hprt ⟨d, hd⟩)

omit [Invertible (2 : R)] in
theorem letterAtR_prt (X : GlueData Φ) (G : Fin X.nc → R) (d : CD Φ) (hd : d ∈ X.t) :
    X.Dg.letterAtR G (X.φc ⟨coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) d, (prt_mem_iff Φ X.hmem d).mpr hd⟩) =
      - X.Dg.letterAtR G (X.φc ⟨d, hd⟩) := by
  rw [← prt_mk, X.hpart, ChordDiagram.letterAtR_partner]

omit [Invertible (2 : R)] in

theorem dval_cOfG (X : GlueData Φ) (G : Fin X.nc → R) (d : CD Φ) (hd : d ∈ X.t) :
    dval Φ (cOfG X G) d = X.Dg.letterAtR G (X.φc ⟨d, hd⟩) := by
  obtain ⟨j, sl⟩ := d
  obtain ⟨w, rfl⟩ := (eV Φ).surjective j
  fin_cases sl
  · replace hd : fdart Φ w 0 ∈ X.t := hd
    show dval Φ (cOfG X G) (eV Φ w, 0) = X.Dg.letterAtR G (X.φc ⟨fdart Φ w 0, hd⟩)
    rw [dval_slot0, cOfG, dif_pos hd]
  · replace hd : (eV Φ w, (1 : Fin 4)) ∈ X.t := hd
    show dval Φ (cOfG X G) (eV Φ w, 1) = X.Dg.letterAtR G (X.φc ⟨(eV Φ w, 1), hd⟩)
    have hp : fdart Φ ((sanL 0)⁻¹ • w) 0 ∈ X.t := by
      rw [show fdart Φ ((sanL 0)⁻¹ • w) 0 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 1) by
        rw [fdart, ← permL_symm_eV]; rfl]
      exact (prt_mem_iff Φ X.hmem _).mpr hd
    have key : (⟨fdart Φ ((sanL 0)⁻¹ • w) 0, hp⟩ : ↥X.t) =
        ⟨coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 1), (prt_mem_iff Φ X.hmem _).mpr hd⟩ :=
      Subtype.ext (by show fdart Φ ((sanL 0)⁻¹ • w) 0 = _; rw [fdart, ← permL_symm_eV]; rfl)
    rw [dval_slot1, cOfG, dif_pos hp, key, letterAtR_prt, neg_neg]
  · replace hd : (eV Φ w, (2 : Fin 4)) ∈ X.t := hd
    show dval Φ (cOfG X G) (eV Φ w, 2) = X.Dg.letterAtR G (X.φc ⟨(eV Φ w, 2), hd⟩)
    have hp : fdart Φ ((sanL 1)⁻¹ • w) 1 ∈ X.t := by
      rw [show fdart Φ ((sanL 1)⁻¹ • w) 1 = coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 2) by
        rw [fdart, ← permL_symm_eV]; rfl]
      exact (prt_mem_iff Φ X.hmem _).mpr hd
    have key : (⟨fdart Φ ((sanL 1)⁻¹ • w) 1, hp⟩ : ↥X.t) =
        ⟨coverPrtFun (mV Φ) (permL Φ 0) (permL Φ 1) (eV Φ w, 2), (prt_mem_iff Φ X.hmem _).mpr hd⟩ :=
      Subtype.ext (by show fdart Φ ((sanL 1)⁻¹ • w) 1 = _; rw [fdart, ← permL_symm_eV]; rfl)
    rw [dval_slot2, cOfG, dif_pos hp, key, letterAtR_prt, neg_neg]
  · replace hd : fdart Φ w 1 ∈ X.t := hd
    show dval Φ (cOfG X G) (eV Φ w, 3) = X.Dg.letterAtR G (X.φc ⟨fdart Φ w 1, hd⟩)
    rw [dval_slot3, cOfG, dif_pos hd]

omit [Invertible (2 : R)] in
theorem dSum_dval_cOfG (X : GlueData Φ) (G : Fin X.nc → R) (q : Fin (2 * X.nc)) :
    dSum X (dval Φ (cOfG X G)) q = X.Dg.faceSumR G q := by
  unfold dSum ChordDiagram.faceSumR
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dval_cOfG X G _ (X.φc.symm _).2, ChordDiagram.perm_pow_apply]
  simp

omit [Invertible (2 : R)] in
theorem cOfG_mem_parKer (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) (G : X.Dg.faceKer (R := R)) :
    cOfG X (G : Fin X.nc → R) ∈ parKer (R := R) Φ := by
  have htree : cOfG X (G : Fin X.nc → R) ∈ treeKer (R := R) Φ := fun w i ht => cOfG_tree X _ w i ht
  refine ⟨fun w i ht => cOfG_tree X _ w i ht, fun i v => ?_⟩
  rw [← cSum_dval_sdart, cSum_sdart_any hΦs, cSum_sdart_eq_dSum_Θ hΦs X _ (dval_eq_zero_of_notMem X _ htree),
    dSum_dval_cOfG]
  exact G.2 _

theorem αFun_surjective (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) : Function.Surjective (αFun hΦs X (R := R)) := by
  intro G
  refine ⟨(parCoord Φ hΦs).symm ⟨cOfG X (G : Fin X.nc → R), cOfG_mem_parKer hΦs X G⟩, Subtype.ext ?_⟩
  rw [αFun_coe]
  have hc : edgeVal Φ hΦs (((parCoord Φ hΦs).symm ⟨cOfG X (G : Fin X.nc → R), cOfG_mem_parKer hΦs X G⟩ :
      ↥(parSub Φ R)) : Additive Φ →+ R) = cOfG X (G : Fin X.nc → R) := by
    rw [← parCoord_apply, LinearEquiv.apply_symm_apply]
  rw [hc]
  funext j
  show dval Φ (cOfG X (G : Fin X.nc → R)) ((X.φc.symm (X.Dg.pos j) : ↥X.t) : CD Φ) = (G : Fin X.nc → R) j
  rw [dval_cOfG X _ _ (X.φc.symm _).2]
  simp [ChordDiagram.letterAtR_pos]

noncomputable def α (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) : ↥(parSub Φ R) ≃ₗ[R] X.Dg.faceKer (R := R) :=
  LinearEquiv.ofBijective (αFun hΦs X) ⟨αFun_injective hΦs X, αFun_surjective hΦs X⟩

theorem α_coe (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ) (ψ : ↥(parSub Φ R)) :
    ((α hΦs X ψ : X.Dg.faceKer (R := R)) : Fin X.nc → R) = GOf X (edgeVal Φ hΦs (ψ : Additive Φ →+ R)) :=
  rfl

theorem pairF_eq_neg_faceFormRBilin [IsFreeGroup Φ] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup) (X : GlueData Φ)
    (φ ψ : ↥(parSub Φ R)) :
    pairF Φ (φ : Additive Φ →+ R) (ψ : Additive Φ →+ R) = - X.Dg.faceFormRBilin (α hΦs X φ) (α hΦs X ψ) := by
  rw [ChordDiagram.faceFormRBilin_apply, α_coe, α_coe]
  exact pairF_eq_neg_faceFormR hΦs X _ _ φ.2 ψ.2

theorem pairF_perfect_of_le_sanov [IsFreeGroup Φ] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup)
    (l : ↥(parSub Φ R) →ₗ[R] R) :
    ∃! φ₀ : ↥(parSub Φ R), ∀ ψ : ↥(parSub Φ R), pairF Φ (φ₀ : Additive Φ →+ R) (ψ : Additive Φ →+ R) = l ψ := by
  obtain ⟨X⟩ := nonempty_glueData Φ
  obtain ⟨G₀, hG₀, huniq⟩ := X.Dg.faceFormR_perfect (-(l.comp (α hΦs X).symm.toLinearMap))
  have hG₀' : ∀ G, X.Dg.faceFormRBilin G₀ G = - l ((α hΦs X).symm G) := fun G => by rw [hG₀]; rfl
  refine ⟨(α hΦs X).symm G₀, fun ψ => ?_, fun φ₁ hφ₁ => ?_⟩
  · rw [pairF_eq_neg_faceFormRBilin hΦs X, LinearEquiv.apply_symm_apply, hG₀', neg_neg, LinearEquiv.symm_apply_apply]
  · have hα : α hΦs X φ₁ = G₀ := by
      refine huniq (α hΦs X φ₁) fun G => ?_
      have h := hφ₁ ((α hΦs X).symm G)
      rw [pairF_eq_neg_faceFormRBilin hΦs X, LinearEquiv.apply_symm_apply] at h
      show X.Dg.faceFormRBilin (α hΦs X φ₁) G = - l ((α hΦs X).symm G)
      rw [← h, neg_neg]
    rw [← hα, LinearEquiv.symm_apply_apply]

end Inv2
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

end Alpha
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
end Transfer
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

section Row

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period"

theorem pairZ_nondeg_modp [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') :=
  P1_of_wall N p hp hp5 fun l' =>
    pairF_perfect_of_le_sanov (Φ := Gamma0 N ⊓ Gamma 4) (inf_le_right.trans gamma_four_le_sanov) l'

end Row
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

end ModularCurve.PDPairing.Glue
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Glue"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord.ChordDiagram P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Chord P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS4 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.CDS5 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover.Fatgraph P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.PDPairing.Cover P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.PDPairing.TD"

open CongruenceSubgroup _root_.ModularCurve.Period _root_.P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.ModularCurve.Period in
theorem solution (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') :=
  ModularCurve.PDPairing.Glue.pairZ_nondeg_modp N p hp hp5

end S_ModularCurve_PDPairing_pairZ_nondegenerate_mod
end P2MW
export P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod (solution)
