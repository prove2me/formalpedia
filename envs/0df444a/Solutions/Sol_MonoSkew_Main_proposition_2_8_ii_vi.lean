-- Prove2me | solution 1 for MonoSkew.Main.proposition_2_8_ii_vi
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T12:40:02.376654+00:00
-- url     : https://prove2.me/submissions/d29e29af-19e0-47ac-b5f7-7314ec3f6b4d

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open MonoSkew.Main

/-- Proposition 2.8(ii)–(vi) (pp. 8–9): in the setting of Problems 1.1 and 1.2, the following are
equivalent: (ii) `z ∈ ran(A + L* ∘ B ∘ (L · − r))`; (iii) `𝒫 ≠ ∅`; (iv) `zer(M + S) ≠ ∅`;
(v) `𝒟 ≠ ∅`; (vi) `−r ∈ ran(−L ∘ A⁻¹ ∘ (z − L*·) + B⁻¹)`. -/
theorem solution {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    List.TFAE
      [∃ x, z ∈ primalOp A B L r x,
       (primalSet A B L z r).Nonempty,
       (zer (addSingle (opM A B z r) (opS L))).Nonempty,
       (dualSet A B L z r).Nonempty,
       ∃ v, -r ∈ dualOp A B L z v] := by
  have hpr : ∀ x, x ∈ primalSet A B L z r ↔
      ∃ v, z - L.adjoint v ∈ A x ∧ v ∈ B (L x - r) := by
    intro x
    constructor
    · rintro ⟨u, hu, w, ⟨v, hv, rfl⟩, he⟩
      exact ⟨v, by convert hu using 1 <;> (rw [he]; abel), hv⟩
    · rintro ⟨v, hv, hb⟩
      exact ⟨z - L.adjoint v, hv, L.adjoint v, ⟨v, hb, rfl⟩, by abel⟩
  have hdu : ∀ v, v ∈ dualSet A B L z r ↔
      ∃ x, z - L.adjoint v ∈ A x ∧ v ∈ B (L x - r) := by
    intro v
    constructor
    · rintro ⟨x, hx, t, ht, he⟩
      refine ⟨x, hx, ?_⟩
      have ht' : t = L x - r := by linear_combination (norm := module) -he
      simpa only [ht', opInv, Set.mem_setOf_eq] using ht
    · rintro ⟨x, hx, hv⟩
      exact ⟨x, hx, L x - r, hv, by abel⟩
  have hze : ∀ w : K H G, w ∈ zer (addSingle (opM A B z r) (opS L)) ↔
      z - L.adjoint w.snd ∈ A w.fst ∧ w.snd ∈ B (L w.fst - r) := by
    intro w
    constructor
    · rintro ⟨u, ⟨hu, hv⟩, he⟩
      have he1 := congrArg WithLp.fst he
      have he2 := congrArg WithLp.snd he
      change 0 = u.fst + L.adjoint w.snd at he1
      change 0 = u.snd + -(L w.fst) at he2
      have hu' : u.fst + z = z - L.adjoint w.snd := by linear_combination (norm := module) -he1
      have hv' : u.snd - r = L w.fst - r := by linear_combination (norm := module) -he2
      exact ⟨by simpa only [hu'] using hu, by simpa only [opInv, hv', Set.mem_setOf_eq] using hv⟩
    · rintro ⟨hx, hv⟩
      refine ⟨WithLp.toLp 2 (-L.adjoint w.snd, L w.fst), ?_, ?_⟩
      · constructor
        · change -L.adjoint w.snd + z ∈ A w.fst
          simpa only [sub_eq_add_neg, add_comm] using hx
        · exact hv
      · apply WithLp.ofLp_injective
        apply Prod.ext <;> simp [opS]
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨v, hx, hv⟩ := (hpr x).mp hx
      exact ⟨WithLp.toLp 2 (x,v), (hze _).mpr ⟨hx,hv⟩⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.fst, (hpr _).mpr ⟨w.snd, (hze _).mp hw⟩⟩
  tfae_have 3 ↔ 4 := by
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w.snd, (hdu _).mpr ⟨w.fst, (hze _).mp hw⟩⟩
    · rintro ⟨v, hv⟩
      obtain ⟨x,hx,hv⟩ := (hdu v).mp hv
      exact ⟨WithLp.toLp 2 (x,v), (hze _).mpr ⟨hx,hv⟩⟩
  tfae_have 4 ↔ 5 := Iff.rfl
  tfae_finish



