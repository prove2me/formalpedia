-- Prove2me | solution 1 for LovaszSchrijver.OddHole.NG_eq_odd_hole_system
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T00:26:37.225266+00:00
-- url     : https://prove2.me/submissions/3224afe4-cc24-4b88-9d86-a6070de3bc6c

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_OddHole
import Definitions.Def_LovaszSchrijver_OddHole_AlternatingWalk
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction
import Definitions.Def_LovaszSchrijver_OddHole_FacetHyperplanes

set_option autoImplicit false

/- Complete checked body: AttributedOddHole -/
section


/- Complete attributed source: Sol_LovaszSchrijver_OddHole_M_FR_entry_eq_zero_of_adj -/
section
-- Prove2me | solution 1 for LovaszSchrijver.OddHole.M_FR_entry_eq_zero_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:21.436475+00:00
-- url     : https://prove2.me/submissions/40b1daf5-f7da-4330-a574-d494712211c4


namespace LovaszSchrijver.OddHole

theorem aux_mfr0_Q_nonneg {V : Type} (x : Option V → ℝ) (hx : x ∈ Q V) (k : V) :
    0 ≤ x (some k) := by
  unfold Q at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy.2 k with h | h <;> simp [h]
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply]; linarith
  | smul c a _ ha =>
    rw [Pi.smul_apply]
    change 0 ≤ (c : ℝ) * a (some k)
    exact mul_nonneg c.2 ha

theorem aux_mfr0_single_dual_Q {V : Type} [Fintype V] [DecidableEq V] (k : V) :
    (Pi.single (some k) 1 : Option V → ℝ) ∈ dualCone (Q V) := by
  intro x hx
  rw [single_dotProduct, one_mul]
  exact aux_mfr0_Q_nonneg x hx k

theorem aux_mfr0_single_dual_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : V) : (Pi.single (some k) 1 : Option V → ℝ) ∈ dualCone (FR G) := by
  intro x hx
  rw [single_dotProduct, one_mul]
  exact hx.1 k

theorem aux_mfr0_edge_dual_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i j : V) (hij : G.Adj i j) :
    (Pi.single none 1 - Pi.single (some i) 1 - Pi.single (some j) 1 : Option V → ℝ)
      ∈ dualCone (FR G) := by
  intro x hx
  rw [sub_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  have := hx.2 i j hij
  linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem checked_M_FR_entry_eq_zero_of_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hG : ∀ v, ∃ w, G.Adj v w)
    (Y : Matrix (Option V) (Option V) ℝ) (hY : Y ∈ M (FR G) (Q V))
    (i j : V) (hij : G.Adj i j) :
    Y (some i) (some j) = 0 := by
  obtain ⟨_, hdiag, hpos⟩ := hY
  have h1 := hpos _ (aux_mfr0_edge_dual_FR G i j hij) _ (aux_mfr0_single_dual_Q j)
  have h2 := hpos _ (aux_mfr0_single_dual_FR G i) _ (aux_mfr0_single_dual_Q j)
  rw [Matrix.mulVec_single_one] at h1 h2
  rw [sub_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct,
    single_dotProduct] at h1
  rw [single_dotProduct] at h2
  simp only [Matrix.col_apply, one_mul] at h1 h2
  have hd := hdiag j
  linarith

end

/- Complete attributed source: Sol_LovaszSchrijver_OddHole_N_subset_H_add_G -/
section
-- Prove2me | solution 1 for LovaszSchrijver.OddHole.N_subset_H_add_G
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:25:07.968902+00:00
-- url     : https://prove2.me/submissions/cd3731fb-ea78-4ce5-ba57-f4b1037bf46e


open Pointwise

namespace LovaszSchrijver.OddHole

/-- Separation: a point outside a closed convex cone is separated by a dual vector. -/
theorem aux_nshg_sep {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (x : Option ι → ℝ) (hx : x ∉ K) :
    ∃ u ∈ dualCone K, dotProduct u x < 0 := by
  obtain ⟨hne, hadd, hsmul⟩ := hK
  have hconv : Convex ℝ K := by
    intro a ha b hb s t hs ht _
    exact hadd _ (hsmul s hs a ha) _ (hsmul t ht b hb)
  obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed hconv hKc hx
  obtain ⟨k0, hk0⟩ := hne
  have h0 : (0 : Option ι → ℝ) ∈ K := by
    have := hsmul 0 le_rfl k0 hk0
    simpa using this
  have hu : u < 0 := by
    have := hfK 0 h0
    simpa using this
  have hfnn : ∀ b ∈ K, 0 ≤ f b := by
    intro b hb
    by_contra hneg
    push Not at hneg
    have hc : 0 ≤ u / f b := div_nonneg_of_nonpos hu.le hneg.le
    have := hfK _ (hsmul (u / f b) hc b hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  have hrep : ∀ y : Option ι → ℝ,
      dotProduct (fun j => f (Pi.single j 1)) y = f y := by
    intro y
    conv_rhs => rw [← Finset.univ_sum_single y]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : (Pi.single j (y j) : Option ι → ℝ) = y j • Pi.single j 1 := by
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
  · intro b hb
    rw [hrep]
    exact hfnn b hb
  · rw [hrep]
    linarith

/-- Membership in the dual of `Q` for functionals nonnegative on the generators. -/
theorem aux_nshg_dualQ {ι : Type} [Fintype ι] (v : Option ι → ℝ)
    (hv : ∀ x : Option ι → ℝ, (x none = 1 ∧ ∀ i : ι, x (some i) = 0 ∨ x (some i) = 1) →
      0 ≤ dotProduct v x) :
    v ∈ dualCone (Q ι) := by
  intro x hx
  unfold Q at hx
  simp only [SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hv y hy
  | zero => simp
  | add y z _ _ hy hz => rw [dotProduct_add]; exact add_nonneg hy hz
  | smul a y _ hy =>
    show 0 ≤ v ⬝ᵥ ((a : ℝ) • y)
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_nonneg a.2 hy

theorem aux_nshg_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (Y : Matrix (Option ι) (Option ι) ℝ) (hY : Y ∈ M K (Q ι))
    (v : Option ι → ℝ) (hv : v ∈ dualCone (Q ι)) :
    Y.mulVec v ∈ K := by
  by_contra hno
  obtain ⟨u, hu, hlt⟩ := aux_nshg_sep K hK hKc _ hno
  have := hY.2.2 u hu v hv
  linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole
open Pointwise

theorem checked_N_subset_H_add_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (_hKQ : K ⊆ Q ι)
    (i : ι) :
    N K ⊆ (K ∩ Hplane i) + (K ∩ Gplane i) := by
  intro x hx
  obtain ⟨Y, hY, rfl⟩ := hx
  set e0 : Option ι → ℝ := Pi.single none 1 with he0
  set ei : Option ι → ℝ := Pi.single (some i) 1 with hei
  have hd1 : e0 - ei ∈ dualCone (Q ι) := by
    apply aux_nshg_dualQ
    intro x ⟨hx0, hxi⟩
    rw [sub_dotProduct, he0, hei, single_dotProduct, single_dotProduct, hx0]
    rcases hxi i with h | h <;> rw [h] <;> norm_num
  have hd2 : ei ∈ dualCone (Q ι) := by
    apply aux_nshg_dualQ
    intro x ⟨_, hxi⟩
    rw [hei, single_dotProduct]
    rcases hxi i with h | h <;> rw [h] <;> norm_num
  have hsymm := hY.1
  have hdiag := hY.2.1 i
  refine Set.mem_add.mpr ⟨Y.mulVec (e0 - ei), ⟨aux_nshg_mem K hK hKc Y hY _ hd1, ?_⟩,
    Y.mulVec ei, ⟨aux_nshg_mem K hK hKc Y hY _ hd2, ?_⟩, ?_⟩
  · show (Y.mulVec (e0 - ei)) (some i) = 0
    rw [Matrix.mulVec_sub, Pi.sub_apply, he0, hei, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    rw [hsymm.apply none (some i), hdiag]
    ring
  · show (Y.mulVec ei) (some i) = (Y.mulVec ei) none
    rw [hei, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply]
    exact hdiag
  · rw [← Matrix.mulVec_add, sub_add_cancel]

end

/- Complete attributed source: Sol_LovaszSchrijver_OddHole_odd_hole_deletion_contraction_valid_FRAC -/
section
-- Prove2me | solution 1 for LovaszSchrijver.OddHole.odd_hole_deletion_contraction_valid_FRAC
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:51:29.545401+00:00
-- url     : https://prove2.me/submissions/60f03e42-027f-4fcf-b521-030e67366374


namespace LovaszSchrijver.OddHole

section aux_odhdc
open Fin.NatCast Fin.CommRing

theorem aux_odhdc_pair (x : ℕ → ℝ) : ∀ n : ℕ,
    (∀ j < n, x (2 * j) + x (2 * j + 1) ≤ 1) → ∑ u ∈ Finset.range (2 * n), x u ≤ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    push_cast
    linarith

theorem aux_odhdc_reindex {V : Type} [Fintype V] (C : Finset V) (m : ℕ) [NeZero m]
    (f : Fin m ≃ C) (s : Fin m) (b x : V → ℝ) (hb : ∀ j, j ∉ C → b j = 0) :
    ∑ j, b j * x j = ∑ u ∈ Finset.range m,
      b ((f ((u : Fin m) + s) : C) : V) * x ((f ((u : Fin m) + s) : C) : V) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ C) (fun j _ hj => by simp [hb j hj])]
  rw [← Finset.sum_coe_sort C]
  rw [← Equiv.sum_comp f]
  rw [← Equiv.sum_comp (Equiv.addRight s)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun u => b ((f ((u : Fin m) + s) : C) : V) * x ((f ((u : Fin m) + s) : C) : V))]
  simp [Fin.cast_val_eq_self]

theorem aux_odhdc_main {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) := by
  obtain ⟨m, hmodd, hm3, f, hf⟩ := hC
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 3 := by
    obtain ⟨j, hj⟩ := hmodd; exact ⟨j - 1, by omega⟩
  have hcard : (C.card : ℝ) = 2 * k + 3 := by
    have := Fintype.card_congr f
    simp at this
    rw [← this]; push_cast; ring
  set s : Fin (2 * k + 3) := f.symm ⟨i, hi⟩ with hs
  have hfs : ((f s : C) : V) = i := by simp [hs]
  have hadj : ∀ t : Fin (2 * k + 3), G.Adj ((f t : C) : V) ((f (t + 1) : C) : V) := by
    intro t
    rw [hf]
    left
    rw [Fin.val_add, Fin.val_one]
  have hlast : ((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s + 1 = s := by
    have h0 : ((2 * k + 3 : ℕ) : Fin (2 * k + 3)) = 0 := Fin.natCast_self _
    push_cast at h0 ⊢
    linear_combination h0
  have hstep : ∀ u : ℕ, ((u + 1 : ℕ) : Fin (2 * k + 3)) + s = ((u : ℕ) : Fin (2 * k + 3)) + s + 1 := by
    intro u; push_cast; ring
  constructor
  · intro x hx
    obtain ⟨hx0, hxe⟩ := hx
    rw [aux_odhdc_reindex C (2 * k + 3) f s _ x (by
      intro j hj; simp [deletion, Function.update_apply, hj])]
    rw [Finset.sum_range_succ']
    have hz : deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i
        ((f (((0 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 := by
      simp [hfs, deletion]
    rw [hz, zero_mul, add_zero]
    have hle : ∀ u ∈ Finset.range (2 * k + 2),
        deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i
          ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) *
          x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) ≤
        x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) := by
      intro u _
      have h0 := hx0 ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)
      simp only [deletion, Function.update_apply]
      split_ifs <;> nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    have hp := aux_odhdc_pair (fun u => x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V))
      (k + 1) (by
        intro j _
        rw [hstep (2 * j + 1)]
        exact hxe _ _ (hadj _))
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hp
    rw [hcard]
    push_cast at hp ⊢
    linarith
  · intro x hx
    obtain ⟨hx0, hxe⟩ := hx
    set b := contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i with hb
    rw [aux_odhdc_reindex C (2 * k + 3) f s b x (by intro j hj; simp [hb, contraction, hj])]
    have hbi : ∀ t : Fin (2 * k + 3),
        ((f t : C) : V) = i ∨ G.Adj i ((f t : C) : V) → b ((f t : C) : V) = 0 := by
      intro t ht; simp [hb, contraction, ht]
    have e1 : b ((f (((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inr (by
        have := hadj (((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s)
        rw [hlast, hfs] at this
        exact this.symm))
    have e2 : b ((f (((0 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inr (by
        rw [hstep 0]
        simp only [Nat.cast_zero, zero_add]
        rw [← hfs]
        exact hadj s))
    have e3 : b ((f (((0 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inl (by simp [hfs]))
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    rw [e1, e2, e3]
    simp only [zero_mul, add_zero]
    have hle : ∀ u ∈ Finset.range (2 * k),
        b ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) *
          x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) ≤
        x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) := by
      intro u _
      have h0 := hx0 ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)
      simp only [hb, contraction]
      split_ifs <;> nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    have hp := aux_odhdc_pair
      (fun u => x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)) k (by
        intro j _
        rw [hstep (2 * j + 1 + 1)]
        exact hxe _ _ (hadj _))
    rw [hcard]
    push_cast at hp ⊢
    linarith

end aux_odhdc

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem checked_odd_hole_deletion_contraction_valid_FRAC {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) :=
  aux_odhdc_main G hG C hC i hi

end

/- Complete attributed source: Sol_LovaszSchrijver_OddHole_two_var_system_infeasible_iff -/
section
-- Prove2me | solution 1 for LovaszSchrijver.OddHole.two_var_system_infeasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:41:44.283784+00:00
-- url     : https://prove2.me/submissions/e84331bc-bc99-40cf-90b8-8eba35d90832


namespace LovaszSchrijver.OddHole

theorem aux_tvs_altB_succ {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 2) → W) :
    altB a b v = b s(v 0, v 1) + altA a b (Fin.tail v) := by
  unfold altB altA
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, Even.zero, if_true,
    Fin.val_succ, Nat.even_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.tail, Fin.succ_castSucc]
  split_ifs <;> rfl

theorem aux_tvs_altA_succ {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 2) → W) :
    altA a b v = -a s(v 0, v 1) + altB a b (Fin.tail v) := by
  unfold altB altA
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, Even.zero, if_true,
    Fin.val_succ, Nat.even_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.tail, Fin.succ_castSucc]
  split_ifs <;> rfl

theorem aux_tvs_walk_tail {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 2) → W)
    (hv : IsWalkSeq H v) : IsWalkSeq H (Fin.tail v) := by
  intro t
  show H.Adj (v t.castSucc.succ) (v t.succ.succ)
  rw [Fin.succ_castSucc]
  exact hv t.succ

theorem aux_tvs_walk_cons {W : Type} (H : SimpleGraph W) {p : ℕ} (i : W) (w : Fin (p + 1) → W)
    (hw : IsWalkSeq H w) (hi : H.Adj i (w 0)) :
    IsWalkSeq H (Fin.cons i w : Fin (p + 2) → W) := by
  intro t
  refine Fin.cases ?_ ?_ t
  · simpa using hi
  · intro s
    have := hw s
    simpa [← Fin.succ_castSucc] using this

theorem aux_tvs_rev_walk {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 1) → W)
    (hv : IsWalkSeq H v) : IsWalkSeq H (fun t => v (Fin.rev t)) := by
  intro t
  simp only [Fin.rev_castSucc, Fin.rev_succ]
  exact (hv (Fin.rev t)).symm

theorem aux_tvs_rev_altB {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W)
    (hp : Even p) : altB a b (fun t => v (Fin.rev t)) = altA a b v := by
  unfold altB altA
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
  have hpar : Even (Fin.rev t).val ↔ ¬ Even t.val := by
    rw [Fin.val_rev, Nat.even_sub (by omega), Nat.even_add_one]
    tauto
  rw [Sym2.eq_swap (a := v t.succ)]
  by_cases ht : Even t.val
  · rw [if_neg (by tauto), if_pos ht]
  · rw [if_pos (by tauto), if_neg ht]

theorem aux_tvs_tele {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (y : W → ℝ)
    (hy : ∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) :
    ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v →
      y (v 0) + (-1 : ℝ) ^ (p + 1) * y (v (Fin.last p)) ≤ altB a b v ∧
      -(y (v 0) + (-1 : ℝ) ^ (p + 1) * y (v (Fin.last p))) ≤ altA a b v := by
  intro p
  induction p with
  | zero =>
    intro v _
    have : (Fin.last 0) = (0 : Fin 1) := rfl
    simp [altB, altA, this]
  | succ q ih =>
    intro v hv
    have h0 := hy _ _ (hv 0)
    obtain ⟨h1, h2⟩ := ih (Fin.tail v) (aux_tvs_walk_tail H v hv)
    rw [aux_tvs_altB_succ, aux_tvs_altA_succ]
    have e1 : Fin.tail v 0 = v 1 := rfl
    have e2 : Fin.tail v (Fin.last q) = v (Fin.last (q + 1)) := by
      simp [Fin.tail, Fin.succ_last]
    have e3 : (Fin.castSucc (0 : Fin (q + 1))) = 0 := rfl
    have e4 : (Fin.succ (0 : Fin (q + 1))) = 1 := rfl
    rw [e1, e2] at h1 h2
    rw [e3, e4] at h0
    have hs : (-1 : ℝ) ^ (q + 1 + 1) = -(-1 : ℝ) ^ (q + 1) := by ring
    rw [hs]
    constructor <;> nlinarith [h0.1, h0.2]

def aux_tvs_Up {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W) (i : W) :
    Set ℝ :=
  {r | ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧ v 0 = i ∧
      (Odd p ∨ (Even p ∧ v (Fin.last p) ∈ U)) ∧ r = altB a b v}

def aux_tvs_Lo {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W) (i : W) :
    Set ℝ :=
  {r | ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧ v 0 = i ∧
      (Even p ∨ (Odd p ∧ v (Fin.last p) ∈ U)) ∧ r = -altA a b v}

theorem aux_tvs_zero_mem_Lo {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i : W) : (0 : ℝ) ∈ aux_tvs_Lo H a b U i := by
  refine ⟨0, fun _ => i, fun t => t.elim0, rfl, Or.inl Even.zero, ?_⟩
  simp [altA]

theorem aux_tvs_zero_mem_Up {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i : W) (hi : i ∈ U) : (0 : ℝ) ∈ aux_tvs_Up H a b U i := by
  refine ⟨0, fun _ => i, fun t => t.elim0, rfl, Or.inr ⟨Even.zero, hi⟩, ?_⟩
  simp [altB]

theorem aux_tvs_Up_cons {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i j : W) (hij : H.Adj i j) (r : ℝ) (hr : r ∈ aux_tvs_Lo H a b U j) :
    b s(i, j) - r ∈ aux_tvs_Up H a b U i := by
  obtain ⟨p, w, hw, hw0, hpar, rfl⟩ := hr
  refine ⟨p + 1, Fin.cons i w, aux_tvs_walk_cons H i w hw (hw0 ▸ hij), rfl, ?_, ?_⟩
  · rcases hpar with h | ⟨h, hU⟩
    · exact Or.inl h.add_one
    · exact Or.inr ⟨h.add_one, by simpa [Fin.cons_last] using hU⟩
  · rw [aux_tvs_altB_succ]
    simp [Fin.cons_one, Fin.tail_cons, hw0]

theorem aux_tvs_Lo_cons {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i j : W) (hij : H.Adj i j) (r : ℝ) (hr : r ∈ aux_tvs_Up H a b U j) :
    a s(i, j) - r ∈ aux_tvs_Lo H a b U i := by
  obtain ⟨p, w, hw, hw0, hpar, rfl⟩ := hr
  refine ⟨p + 1, Fin.cons i w, aux_tvs_walk_cons H i w hw (hw0 ▸ hij), rfl, ?_, ?_⟩
  · rcases hpar with h | ⟨h, hU⟩
    · exact Or.inl h.add_one
    · exact Or.inr ⟨h.add_one, by simpa [Fin.cons_last] using hU⟩
  · rw [aux_tvs_altA_succ]
    simp [Fin.cons_one, Fin.tail_cons, hw0]
    ring

theorem aux_tvs_construct {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (U : Finset W)
    (hA : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Odd p → 0 ≤ altB a b v)
    (hC : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Even p → v (Fin.last p) ∈ U →
      0 ≤ altB a b v)
    (hD : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Odd p → v 0 ∈ U →
      v (Fin.last p) ∈ U → 0 ≤ altA a b v) :
    ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0) := by
  -- basic facts
  have Up_nonneg : ∀ i, ∀ r ∈ aux_tvs_Up H a b U i, 0 ≤ r := by
    rintro i r ⟨p, v, hv, _, hpar, rfl⟩
    rcases hpar with h | ⟨h, hU⟩
    · exact hA p v hv h
    · exact hC p v hv h hU
  have Up_bdd : ∀ i, BddBelow (aux_tvs_Up H a b U i) := fun i => ⟨0, Up_nonneg i⟩
  have Lo_bdd : ∀ i, BddAbove (aux_tvs_Lo H a b U i) := by
    intro i
    refine ⟨∑ z : W, |b s(z, i)|, ?_⟩
    intro r hr
    have hr' := hr
    obtain ⟨p, w, hw, hw0, hpar, hrw⟩ := hr
    rcases p with _ | q
    · rw [hrw]; simp only [altA, Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
      exact Finset.sum_nonneg (fun z _ => abs_nonneg _)
    · have hadj : H.Adj (w 1) i := by
        have := hw 0
        rw [← hw0]; exact this.symm
      have h1 := Up_nonneg _ _ (aux_tvs_Up_cons H a b U (w 1) i hadj r hr')
      have h2 : b s(w 1, i) ≤ |b s(w 1, i)| := le_abs_self _
      have h3 : |b s(w 1, i)| ≤ ∑ z : W, |b s(z, i)| :=
        Finset.single_le_sum (f := fun z => |b s(z, i)|) (fun z _ => abs_nonneg _)
          (Finset.mem_univ _)
      linarith
  have Lo_ne : ∀ i, (aux_tvs_Lo H a b U i).Nonempty :=
    fun i => ⟨0, aux_tvs_zero_mem_Lo H a b U i⟩
  have Up_ne : ∀ i j, H.Adj i j → (aux_tvs_Up H a b U i).Nonempty :=
    fun i j hij => ⟨_, aux_tvs_Up_cons H a b U i j hij 0 (aux_tvs_zero_mem_Lo H a b U j)⟩
  set P : W → ℝ := fun i => sInf (aux_tvs_Up H a b U i) with hP
  set Q : W → ℝ := fun i => sSup (aux_tvs_Lo H a b U i) with hQ
  have P_nonneg : ∀ i, 0 ≤ P i := fun i => Real.sInf_nonneg (Up_nonneg i)
  have Q_nonneg : ∀ i, 0 ≤ Q i := fun i => le_csSup (Lo_bdd i) (aux_tvs_zero_mem_Lo H a b U i)
  have key1 : ∀ i j, H.Adj i j → P i + Q j ≤ b s(i, j) := by
    intro i j hij
    have : Q j ≤ b s(i, j) - P i := by
      apply csSup_le (Lo_ne j)
      intro r hr
      have := csInf_le (Up_bdd i) (aux_tvs_Up_cons H a b U i j hij r hr)
      simp only [hP] at this ⊢
      linarith
    linarith
  have key2 : ∀ i j, H.Adj i j → a s(i, j) ≤ Q i + P j := by
    intro i j hij
    have : a s(i, j) - Q i ≤ P j := by
      apply le_csInf (Up_ne j i hij.symm)
      intro r hr
      have := le_csSup (Lo_bdd i) (aux_tvs_Lo_cons H a b U i j hij r hr)
      simp only [hQ] at this ⊢
      linarith
    linarith
  refine ⟨fun i => (P i + Q i) / 2, ?_, ?_, ?_⟩
  · intro i j hij
    have k1 := key1 i j hij
    have k1' := key1 j i hij.symm
    have k2 := key2 i j hij
    have k2' := key2 j i hij.symm
    rw [Sym2.eq_swap] at k1' k2'
    constructor <;> simp only <;> linarith
  · intro i
    have := P_nonneg i
    have := Q_nonneg i
    simp only
    linarith
  · intro i hi
    have hP0 : P i ≤ 0 := csInf_le (Up_bdd i) (aux_tvs_zero_mem_Up H a b U i hi)
    have hQ0 : Q i ≤ 0 := by
      apply csSup_le (Lo_ne i)
      rintro r ⟨p, w, hw, hw0, hpar, rfl⟩
      rcases hpar with h | ⟨h, hU⟩
      · have := hC p (fun t => w (Fin.rev t)) (aux_tvs_rev_walk H w hw) h
          (by simpa [hw0] using hi)
        rw [aux_tvs_rev_altB a b w h] at this
        linarith
      · have := hD p w hw h (hw0 ▸ hi) hU
        linarith
    have := P_nonneg i
    have := Q_nonneg i
    simp only
    linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem checked_two_var_system_infeasible_iff {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (_hab : ∀ e ∈ H.edgeSet, 0 ≤ a e ∧ a e ≤ b e) (U : Finset W) :
    (¬ ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0)) ↔
      ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧
        ((Odd p ∧ altB a b v < 0) ∨
         (Even p ∧ v 0 = v (Fin.last p) ∧ altB a b v < 0) ∨
         (Even p ∧ v (Fin.last p) ∈ U ∧ altB a b v < 0) ∨
         (Odd p ∧ v 0 ∈ U ∧ v (Fin.last p) ∈ U ∧ altA a b v < 0)) := by
  constructor
  · intro hno
    by_contra hw
    apply hno
    apply aux_tvs_construct H a b U
    · intro p v hv hp
      by_contra h
      exact hw ⟨p, v, hv, Or.inl ⟨hp, lt_of_not_ge h⟩⟩
    · intro p v hv hp hU
      by_contra h
      exact hw ⟨p, v, hv, Or.inr (Or.inr (Or.inl ⟨hp, hU, lt_of_not_ge h⟩))⟩
    · intro p v hv hp h0 hU
      by_contra h
      exact hw ⟨p, v, hv, Or.inr (Or.inr (Or.inr ⟨hp, h0, hU, lt_of_not_ge h⟩))⟩
  · rintro ⟨p, v, hv, h⟩ ⟨y, hy, hy0, hyU⟩
    obtain ⟨hB, hA⟩ := aux_tvs_tele H a b y hy p v hv
    have n0 := hy0 (v 0)
    have nl := hy0 (v (Fin.last p))
    rcases h with ⟨hp, hlt⟩ | ⟨hp, heq, hlt⟩ | ⟨hp, hU, hlt⟩ | ⟨hp, h0, hU, hlt⟩
    · rw [(show Even (p + 1) from hp.add_one).neg_one_pow] at hB
      linarith
    · rw [(show Odd (p + 1) from hp.add_one).neg_one_pow, ← heq] at hB
      linarith
    · rw [(show Odd (p + 1) from hp.add_one).neg_one_pow, hyU _ hU] at hB
      linarith
    · rw [(show Even (p + 1) from hp.add_one).neg_one_pow, hyU _ hU, hyU _ h0] at hA
      linarith

end
end

/- Complete checked body: MatrixColumns -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole Matrix

theorem dualQ_e0 {V : Type} [Fintype V] [DecidableEq V] :
    (Pi.single none 1 : Option V → ℝ) ∈ dualCone (Q V) := by
  apply aux_nshg_dualQ
  intro x hx
  simp only [single_dotProduct, one_mul, hx.1]
  norm_num

theorem dualQ_complement {V : Type} [Fintype V] [DecidableEq V] (i : V) :
    (Pi.single none 1 - Pi.single (some i) 1 : Option V → ℝ) ∈ dualCone (Q V) := by
  apply aux_nshg_dualQ
  intro x hx
  rw [sub_dotProduct, single_dotProduct, single_dotProduct, hx.1]
  rcases hx.2 i with h | h <;> simp [h]

theorem matrix_action_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {Y : Matrix (Option V) (Option V) ℝ} (hY : Y ∈ M (FR G) (Q V))
    {v : Option V → ℝ} (hv : v ∈ dualCone (Q V)) : Y.mulVec v ∈ FR G := by
  constructor
  · intro i
    have h := hY.2.2 _ (aux_mfr0_single_dual_FR G i) v hv
    simpa only [single_dotProduct, one_mul] using h
  · intro i j hij
    have h := hY.2.2 _ (aux_mfr0_edge_dual_FR G i j hij) v hv
    rw [sub_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct,
      single_dotProduct] at h
    linarith

theorem NG_subset_FRAC {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    NG G ⊆ FRAC G := by
  rintro x ⟨Y, hY, he⟩
  have hh := matrix_action_FR G hY (dualQ_e0 (V := V))
  rw [he] at hh
  exact hh

theorem frac_le_one {V : Type} (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    {x : V → ℝ} (hx : x ∈ FRAC G) (i : V) : x i ≤ 1 := by
  obtain ⟨j, hij⟩ := hG i
  linarith [hx.2 i j hij, hx.1 j]

theorem dualQ_interval_pairing {V : Type} [Fintype V] [DecidableEq V]
    {v : Option V → ℝ} (hv : v ∈ dualCone (Q V)) (z : Option V → ℝ)
    (hz0 : 0 ≤ z none) (hz : ∀ i, 0 ≤ z (some i) ∧ z (some i) ≤ z none) :
    0 ≤ dotProduct z v := by
  classical
  let b : Option V → ℝ := fun o => o.elim 1 (fun i => if v (some i) < 0 then 1 else 0)
  have hb : b ∈ Q V := by
    apply PointedCone.subset_hull
    refine ⟨rfl, ?_⟩
    intro i
    by_cases hi : v (some i) < 0 <;> simp [b, hi]
  have hvsum := hv b hb
  simp only [dotProduct, Fintype.sum_option, b, Option.elim_none, Option.elim_some,
    mul_one] at hvsum
  have he : (∑ i : V, v (some i) * (if v (some i) < 0 then 1 else 0)) =
      ∑ i : V, if v (some i) < 0 then v (some i) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he] at hvsum
  have hterm (i : V) : z none * (if v (some i) < 0 then v (some i) else 0) ≤
      z (some i) * v (some i) := by
    split_ifs with hi
    · exact mul_le_mul_of_nonpos_right (hz i).2 hi.le
    · simpa only [mul_zero] using mul_nonneg (hz i).1 (le_of_not_gt hi)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset V)) => hterm i)
  rw [← Finset.mul_sum] at hs
  have hh := mul_nonneg hz0 hvsum
  unfold dotProduct
  rw [Fintype.sum_option]
  nlinarith

theorem matrix_mem_of_columns {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y : Matrix (Option V) (Option V) ℝ)
    (hsymm : Y.IsSymm) (hdiag : ∀ i, Y (some i) (some i) = Y none (some i))
    (h0 : Y.mulVec (Pi.single none 1) ∈ FR G)
    (hi : ∀ i : V, Y.mulVec (Pi.single (some i) 1) ∈ FR G)
    (hc : ∀ i : V, Y.mulVec (Pi.single none 1 - Pi.single (some i) 1) ∈ FR G) :
    Y ∈ M (FR G) (Q V) := by
  refine ⟨hsymm, hdiag, ?_⟩
  intro u hu v hv
  rw [Matrix.dotProduct_mulVec]
  apply dualQ_interval_pairing hv (Matrix.vecMul u Y)
  · have h := hu _ h0
    rw [Matrix.mulVec_single_one] at h
    change 0 ≤ dotProduct u (fun i => Y i none) at h
    exact h
  · intro i
    have ha := hu _ (hi i)
    have hb := hu _ (hc i)
    rw [Matrix.mulVec_sub, dotProduct_sub, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at hb
    rw [Matrix.mulVec_single_one] at ha
    change 0 ≤ dotProduct u (fun j => Y j (some i)) at ha
    change 0 ≤ dotProduct u (fun j => Y j none) - dotProduct u (fun j => Y j (some i)) at hb
    exact ⟨ha, sub_nonneg.mp hb⟩

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: ForwardValidity -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole Matrix

theorem homogeneous_valid_FR {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hv : Valid (FRAC G) a b) (y : Option V → ℝ) (hy : y ∈ FR G) (hy0 : 0 ≤ y none) :
    (∑ i, a i * y (some i)) ≤ b * y none := by
  by_cases h0 : y none = 0
  · have hi (i : V) : y (some i) = 0 := by
      obtain ⟨j, hij⟩ := hG i
      have hh := hy.2 i j hij
      rw [h0] at hh
      linarith [hy.1 i, hy.1 j]
    simp [hi, h0]
  · have hp : 0 < y none := lt_of_le_of_ne hy0 (Ne.symm h0)
    have hz : (fun i => y (some i) / y none) ∈ FRAC G := by
      refine ⟨fun i => div_nonneg (hy.1 i) hy0, ?_⟩
      intro i j hij
      rw [← add_div, div_le_one₀ hp]
      exact hy.2 i j hij
    have hh := mul_le_mul_of_nonneg_right (hv _ hz) hy0
    simpa only [Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ h0] using hh

theorem deletion_sum_of_zero {V : Type} [Fintype V] [DecidableEq V]
    (a z : V → ℝ) (i : V) (hi : z i = 0) :
    (∑ j, deletion a i j * z j) = ∑ j, a j * z j := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [deletion, hi]
  · simp [deletion, hji]

theorem contraction_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a z : V → ℝ) (i : V)
    (hz : ∀ j, G.Adj i j → z j = 0) :
    (∑ j, a j * z j) = a i * z i + ∑ j, contraction G a i j * z j := by
  have he (j : V) : a j * z j = contraction G a i j * z j +
      (if j = i then a i * z i else 0) := by
    by_cases hji : j = i
    · subst j
      simp [contraction]
    · by_cases hij : G.Adj i j
      · simp [contraction, hji, hij, hz j hij]
      · simp [contraction, hji, hij]
  calc
    _ = ∑ j, (contraction G a i j * z j + if j = i then a i * z i else 0) :=
      Finset.sum_congr rfl (fun j _ => he j)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [add_comm]

theorem odd_hole_valid_NG {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (x : V → ℝ) (hx : x ∈ NG G) (C : Finset V) (hC : IsOddHole G C) :
    ∑ j ∈ C, x j ≤ ((C.card : ℝ) - 1) / 2 := by
  classical
  have hne : C.Nonempty := by
    obtain ⟨m, _, hm, f, _⟩ := hC
    exact ⟨(f ⟨0, by omega⟩).val, (f ⟨0, by omega⟩).property⟩
  obtain ⟨i, hi⟩ := hne
  have hfrac := NG_subset_FRAC G hx
  obtain ⟨Y, hY, hproj⟩ := hx
  have hc0 (j : V) : Y (some j) none = x j := by
    have hh := congrFun hproj (some j)
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, hom, Option.elim_some] using hh
  let A : Option V → ℝ := fun j => Y j (some i)
  let B : Option V → ℝ := fun j => hom x j - A j
  have hA : A ∈ FR G := by
    have hh := matrix_action_FR G hY (aux_mfr0_single_dual_Q i)
    rw [Matrix.mulVec_single_one] at hh
    change A ∈ FR G at hh
    exact hh
  have hB : B ∈ FR G := by
    have hh := matrix_action_FR G hY (dualQ_complement i)
    rw [Matrix.mulVec_sub, hproj, Matrix.mulVec_single_one] at hh
    exact hh
  have hA0 : A none = x i := by
    change Y none (some i) = x i
    rw [← hY.1.apply none (some i), hc0]
  have hAi : A (some i) = x i := (hY.2.1 i).trans hA0
  have hB0 : B none = 1 - x i := by simp only [B, hom, Option.elim_none, hA0]
  have hBi : B (some i) = 0 := by simp only [B, hom, Option.elim_some, hAi, sub_self]
  have hAj (j : V) (hij : G.Adj i j) : A (some j) = 0 :=
    checked_M_FR_entry_eq_zero_of_adj G hG Y hY j i hij.symm
  let a : V → ℝ := fun j => if j ∈ C then 1 else 0
  let b : ℝ := ((C.card : ℝ) - 1) / 2
  obtain ⟨hdel, hcon⟩ := checked_odd_hole_deletion_contraction_valid_FRAC G hG C hC i hi
  have hd := homogeneous_valid_FR G hG (deletion a i) b hdel B hB
    (by rw [hB0]; exact sub_nonneg.mpr (frac_le_one G hG hfrac i))
  have hc := homogeneous_valid_FR G hG (contraction G a i) (b - 1) hcon A hA
    (by rw [hA0]; exact hfrac.1 i)
  rw [hB0] at hd
  rw [hA0] at hc
  have hsumA : (∑ j ∈ C, A (some j)) =
      x i + ∑ j, contraction G a i j * A (some j) := by
    have hh := contraction_sum G a (fun j => A (some j)) i hAj
    simpa [a, hi, hAi] using hh
  have hsumB : (∑ j ∈ C, B (some j)) = ∑ j, deletion a i j * B (some j) := by
    have hh := deletion_sum_of_zero a (fun j => B (some j)) i hBi
    simpa [a] using hh.symm
  have hsum : (∑ j ∈ C, x j) = (∑ j ∈ C, A (some j)) + ∑ j ∈ C, B (some j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [B, hom, Option.elim_some]
    ring
  rw [hsum, hsumA, hsumB]
  change _ ≤ b
  nlinarith

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: EdgeWeights -/
section

set_option autoImplicit false

namespace LovaszSchrijver.OddHoleProof

variable {V : Type*}

def edgeWeight (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u + x v, fun _ _ => add_comm _ _⟩

@[simp] theorem edgeWeight_mk (x : V → ℝ) (u v : V) :
    edgeWeight x s(u,v) = x u + x v := rfl

def edgeWeightSum (x : V → ℝ) (E : Multiset (Sym2 V)) : ℝ :=
  (E.map (edgeWeight x)).sum

@[simp] theorem edgeWeightSum_zero (x : V → ℝ) : edgeWeightSum x 0 = 0 := rfl

@[simp] theorem edgeWeightSum_add (x : V → ℝ) (E F : Multiset (Sym2 V)) :
    edgeWeightSum x (E+F) = edgeWeightSum x E + edgeWeightSum x F := by
  simp [edgeWeightSum]

@[simp] theorem edgeWeightSum_cons (x : V → ℝ) (e : Sym2 V) (E : Multiset (Sym2 V)) :
    edgeWeightSum x (e ::ₘ E) = edgeWeight x e + edgeWeightSum x E := by
  simp [edgeWeightSum]

def incidentCount [DecidableEq V] (E : Multiset (Sym2 V)) (v : V) : ℕ :=
  Multiset.countP (fun e => v ∈ e) E

def oddBoundary [Fintype V] [DecidableEq V] (E : Multiset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => Odd (incidentCount E v))

@[simp] theorem mem_oddBoundary [Fintype V] [DecidableEq V]
    (E : Multiset (Sym2 V)) (v : V) :
    v ∈ oddBoundary E ↔ Odd (incidentCount E v) := by simp [oddBoundary]

@[simp] theorem incidentCount_zero [DecidableEq V] (v : V) :
    incidentCount (0 : Multiset (Sym2 V)) v = 0 := rfl

@[simp] theorem incidentCount_add [DecidableEq V]
    (E F : Multiset (Sym2 V)) (v : V) :
    incidentCount (E+F) v = incidentCount E v + incidentCount F v := by
  simp [incidentCount]

theorem incidentCount_cons [DecidableEq V] (e : Sym2 V) (E : Multiset (Sym2 V)) (v : V) :
    incidentCount (e ::ₘ E) v = incidentCount E v + if v ∈ e then 1 else 0 := by
  exact Multiset.countP_cons _ _ _

theorem edgeWeight_le_one (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ u v, G.Adj u v → x u+x v ≤ 1) :
    ∀ e ∈ G.edgeSet, edgeWeight x e ≤ 1 := by
  intro e
  induction e using Sym2.ind with
  | _ u v => exact hx u v

theorem edgeWeightSum_le_card (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ u v, G.Adj u v → x u+x v ≤ 1)
    (E : Multiset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet) :
    edgeWeightSum x E ≤ (E.card : ℝ) := by
  have h := Multiset.sum_le_card_nsmul (E.map (edgeWeight x)) (1 : ℝ) (by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp ha
    exact edgeWeight_le_one G x hx e (hE e he))
  simpa [edgeWeightSum] using h

def walkWeight (x : V → ℝ) {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : ℝ :=
  edgeWeightSum x (p.edges : Multiset (Sym2 V))

@[simp] theorem walkWeight_nil (x : V → ℝ) (G : SimpleGraph V) (u : V) :
    walkWeight x (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkWeight_cons (x : V → ℝ) {G : SimpleGraph V} {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkWeight x (.cons h p) = x u+x v+walkWeight x p := by
  simp [walkWeight, edgeWeightSum]

@[simp] theorem walkWeight_append (x : V → ℝ) {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkWeight x (p.append q) = walkWeight x p + walkWeight x q := by
  simp [walkWeight, edgeWeightSum, SimpleGraph.Walk.edges_append]

theorem walkWeight_le_length (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ u v, G.Adj u v → x u+x v ≤ 1) {u v : V} (p : G.Walk u v) :
    walkWeight x p ≤ p.length := by
  have h := edgeWeightSum_le_card G x hx (p.edges : Multiset (Sym2 V))
    (fun e he => p.edges_subset_edgeSet (Multiset.mem_coe.mp he))
  simpa [walkWeight] using h

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: PairGraph -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole

abbrev PairVertex (V : Type) := {e : Sym2 V // ¬ e.IsDiag}

def mkPair {V : Type} (i j : V) (h : i ≠ j) : PairVertex V :=
  ⟨s(i,j), by simpa only [Sym2.mk_isDiag_iff] using h⟩

def pairGraph {V : Type} (G : SimpleGraph V) : SimpleGraph (PairVertex V) where
  Adj P Q := ∃ i j k, G.Adj i j ∧ P.val = s(i,k) ∧ Q.val = s(j,k)
  symm := ⟨by
    rintro P Q ⟨i,j,k,hij,hP,hQ⟩
    exact ⟨j,i,k,hij.symm,hQ,hP⟩⟩
  loopless := ⟨by
    rintro P ⟨i,j,k,hij,hP,hQ⟩
    have he : s(i,k) = s(j,k) := hP.symm.trans hQ
    rcases Sym2.rel_iff.mp (Sym2.exact he) with ⟨h,_⟩ | ⟨h,h'⟩
    · exact hij.ne h
    · exact hij.ne (h.trans h')⟩

theorem pairGraph_witness {V : Type} {G : SimpleGraph V} {P Q : PairVertex V}
    (h : (pairGraph G).Adj P Q) :
    ∃ i j k, G.Adj i j ∧ i ≠ k ∧ j ≠ k ∧ P.val = s(i,k) ∧ Q.val = s(j,k) := by
  obtain ⟨i,j,k,hij,hP,hQ⟩ := h
  refine ⟨i,j,k,hij,?_,?_,hP,hQ⟩
  · intro he
    apply P.property
    rw [hP, Sym2.mk_isDiag_iff]
    exact he
  · intro he
    apply Q.property
    rw [hQ, Sym2.mk_isDiag_iff]
    exact he

def pairWeight {V : Type} (x : V → ℝ) (P : PairVertex V) : ℝ := edgeWeight x P.val

noncomputable def commonWeight {V : Type} [DecidableEq V] (x : V → ℝ)
    (P Q : PairVertex V) : ℝ := ∑ v ∈ P.val.toFinset ∩ Q.val.toFinset, x v

theorem commonWeight_symm {V : Type} [DecidableEq V] (x : V → ℝ) (P Q : PairVertex V) :
    commonWeight x P Q = commonWeight x Q P := by simp only [commonWeight, Finset.inter_comm]

noncomputable def pairUpper {V : Type} [DecidableEq V] (x : V → ℝ) : Sym2 (PairVertex V) → ℝ :=
  Sym2.lift ⟨commonWeight x, commonWeight_symm x⟩

noncomputable def pairLower {V : Type} [DecidableEq V] (x : V → ℝ) : Sym2 (PairVertex V) → ℝ :=
  Sym2.lift ⟨fun P Q => pairWeight x P + pairWeight x Q - commonWeight x P Q - 1,
    fun P Q => by dsimp only; rw [commonWeight_symm x P Q]; ring⟩

theorem commonWeight_witness {V : Type} [DecidableEq V] (x : V → ℝ)
    {P Q : PairVertex V} {i j k : V} (hij : i ≠ j)
    (hP : P.val = s(i,k)) (hQ : Q.val = s(j,k)) : commonWeight x P Q = x k := by
  have hi : ({i,k} ∩ {j,k} : Finset V) = {k} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  simp only [commonWeight, hP, hQ, Sym2.toFinset_mk_eq, hi, Finset.sum_singleton]

theorem pair_bounds_witness {V : Type} [DecidableEq V] (x : V → ℝ)
    {P Q : PairVertex V} {i j k : V} (hij : i ≠ j)
    (hP : P.val = s(i,k)) (hQ : Q.val = s(j,k)) :
    pairUpper x s(P,Q) = x k ∧ pairLower x s(P,Q) = x i + x j + x k - 1 := by
  have hc := commonWeight_witness x hij hP hQ
  refine ⟨hc, ?_⟩
  change pairWeight x P + pairWeight x Q - commonWeight x P Q - 1 = _
  rw [hc]
  simp only [pairWeight, hP, hQ, edgeWeight_mk]
  ring

noncomputable def forcedPairs {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (PairVertex V) := by
  classical
  exact Finset.univ.filter (fun P => P.val ∈ G.edgeSet)

@[simp] theorem mem_forcedPairs {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : PairVertex V) : P ∈ forcedPairs G ↔ P.val ∈ G.edgeSet := by
  classical
  simp [forcedPairs]

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: BracingCertificate -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole

noncomputable section

def pairInc {V : Type} [DecidableEq V] (P : PairVertex V) (v : V) : ℕ :=
  if v ∈ P.val then 1 else 0

theorem brace_incidence_even {V : Type} [DecidableEq V]
    {P Q : PairVertex V} {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hP : P.val = s(i,k)) (hQ : Q.val = s(j,k)) (v : V) :
    Even ((if v ∈ s(i,j) then 1 else 0) + pairInc P v + pairInc Q v) := by
  simp only [pairInc, hP, hQ, Sym2.mem_iff]
  by_cases hvi : v = i <;> by_cases hvj : v = j <;> by_cases hvk : v = k <;> simp_all

theorem bracing_certificate {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (x : V → ℝ) :
    ∀ (p : ℕ) (v : Fin (p+1) → PairVertex V), IsWalkSeq (pairGraph G) v →
      ∃ E : Multiset (Sym2 V), E.card = p ∧ (∀ e ∈ E, e ∈ G.edgeSet) ∧
        (∀ w : V, Even (incidentCount E w + pairInc (v 0) w + pairInc (v (Fin.last p)) w)) ∧
        2 * altB (pairLower x) (pairUpper x) v + edgeWeightSum x E =
          (p : ℝ) - (if Even p then 0 else 1) + pairWeight x (v 0) -
          (if Even p then 1 else -1) * pairWeight x (v (Fin.last p)) ∧
        2 * altA (pairLower x) (pairUpper x) v + edgeWeightSum x E =
          (p : ℝ) + (if Even p then 0 else 1) - pairWeight x (v 0) +
          (if Even p then 1 else -1) * pairWeight x (v (Fin.last p)) := by
  intro p
  induction p with
  | zero =>
    intro v _
    refine ⟨0, rfl, by simp, ?_, ?_, ?_⟩
    · intro w
      change Even (0 + pairInc (v 0) w + pairInc (v 0) w)
      exact ⟨pairInc (v 0) w, by omega⟩
    · simp [altB, Fin.last_zero]
    · simp [altA, Fin.last_zero]
  | succ q ih =>
    intro v hv
    obtain ⟨E, hcard, hG, hpar, hB, hA⟩ :=
      ih (Fin.tail v) (aux_tvs_walk_tail (pairGraph G) v hv)
    have ht0 : Fin.tail v 0 = v 1 := rfl
    have htlast : Fin.tail v (Fin.last q) = v (Fin.last (q+1)) := by
      simp [Fin.tail, Fin.succ_last]
    simp only [ht0, htlast] at hpar hB hA
    obtain ⟨i,j,k,hij,hik,hjk,hP,hQ⟩ := pairGraph_witness (hv 0)
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hP hQ
    have he : s(i,j) ∈ G.edgeSet := hij
    have hp := pair_bounds_witness x hij.ne hP hQ
    have hweight : edgeWeight x s(i,j) + 2 * pairUpper x s(v 0,v 1) =
        pairWeight x (v 0) + pairWeight x (v 1) := by
      rw [hp.1]
      simp only [pairWeight, hP, hQ, edgeWeight_mk]
      ring
    have hlower : pairLower x s(v 0,v 1) =
        pairWeight x (v 0) + pairWeight x (v 1) - pairUpper x s(v 0,v 1) - 1 := rfl
    refine ⟨s(i,j) ::ₘ E, by simp [hcard], ?_, ?_, ?_, ?_⟩
    · intro e he'
      rcases Multiset.mem_cons.mp he' with rfl | he'
      · exact he
      · exact hG e he'
    · intro w
      have h1 := brace_incidence_even hij.ne hik hjk hP hQ w
      have h2 := hpar w
      rw [incidentCount_cons]
      rw [Nat.even_iff] at h1 h2 ⊢
      omega
    · rw [aux_tvs_altB_succ, edgeWeightSum_cons]
      by_cases hq : Even q
      · have hqn : ¬ Even (q+1) := Nat.not_even_iff_odd.mpr hq.add_one
        simp only [hq, hqn, ite_true, ite_false, Nat.cast_add, Nat.cast_one, one_mul] at hA ⊢
        nlinarith
      · have hqo : Odd q := Nat.not_even_iff_odd.mp hq
        have hqn : Even (q+1) := hqo.add_one
        simp only [hq, hqn, ite_true, ite_false, Nat.cast_add, Nat.cast_one, one_mul] at hA ⊢
        nlinarith
    · rw [aux_tvs_altA_succ, edgeWeightSum_cons, hlower]
      by_cases hq : Even q
      · have hqn : ¬ Even (q+1) := Nat.not_even_iff_odd.mpr hq.add_one
        simp only [hq, hqn, ite_true, ite_false, Nat.cast_add, Nat.cast_one, one_mul] at hB ⊢
        nlinarith
      · have hqo : Odd q := Nat.not_even_iff_odd.mp hq
        have hqn : Even (q+1) := hqo.add_one
        simp only [hq, hqn, ite_true, ite_false, Nat.cast_add, Nat.cast_one, one_mul] at hB ⊢
        nlinarith

end
end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: BoundaryWeights -/
section

namespace LovaszSchrijver.OddHoleProof

theorem pairWeight_eq_sum {V : Type} [DecidableEq V] (x : V → ℝ) (P : PairVertex V) :
    pairWeight x P = ∑ i ∈ P.val.toFinset, x i := by
  rcases P with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ i j =>
    have hij : i ≠ j := by simpa only [Sym2.mk_isDiag_iff] using he
    simp [pairWeight, Sym2.toFinset_mk_eq, hij]

theorem boundary_subset_pair_union {V : Type} [Fintype V] [DecidableEq V]
    (E : Multiset (Sym2 V)) (P Q : PairVertex V)
    (hp : ∀ v, Even (incidentCount E v + pairInc P v + pairInc Q v)) :
    oddBoundary E ⊆ P.val.toFinset ∪ Q.val.toFinset := by
  intro v hv
  by_contra hn
  have hnot : v ∉ P.val.toFinset ∧ v ∉ Q.val.toFinset := by
    simpa only [Finset.mem_union, not_or] using hn
  have hP : v ∉ P.val := by simpa only [Sym2.mem_toFinset] using hnot.1
  have hQ : v ∉ Q.val := by simpa only [Sym2.mem_toFinset] using hnot.2
  have he := hp v
  simp only [pairInc, if_neg hP, if_neg hQ, add_zero] at he
  exact (Nat.not_even_iff_odd.mpr ((mem_oddBoundary E v).mp hv)) he

theorem boundary_weight_le_pairs {V : Type} [Fintype V] [DecidableEq V]
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (E : Multiset (Sym2 V)) (P Q : PairVertex V)
    (hp : ∀ v, Even (incidentCount E v + pairInc P v + pairInc Q v)) :
    (∑ v ∈ oddBoundary E, x v) ≤ pairWeight x P + pairWeight x Q := by
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (boundary_subset_pair_union E P Q hp)
    (fun v _ _ => hx v)
  have hsum := Finset.sum_union_inter (s₁ := P.val.toFinset) (s₂ := Q.val.toFinset) (f := x)
  have hn : 0 ≤ ∑ v ∈ P.val.toFinset ∩ Q.val.toFinset, x v :=
    Finset.sum_nonneg (fun v _ => hx v)
  rw [pairWeight_eq_sum, pairWeight_eq_sum]
  linarith

theorem incidentCount_singleton {V : Type} [DecidableEq V] (e : Sym2 V) (v : V) :
    incidentCount ({e} : Multiset (Sym2 V)) v = if v ∈ e then 1 else 0 := by
  change incidentCount (e ::ₘ 0) v = _
  rw [incidentCount_cons]
  simp

theorem boundary_append_pair_subset {V : Type} [Fintype V] [DecidableEq V]
    (E : Multiset (Sym2 V)) (P Q : PairVertex V)
    (hp : ∀ v, Even (incidentCount E v + pairInc P v + pairInc Q v)) :
    oddBoundary (E + {Q.val}) ⊆ P.val.toFinset := by
  intro v hv
  by_contra hn
  have hP : v ∉ P.val := by simpa only [Sym2.mem_toFinset] using hn
  have he := hp v
  have ho := (mem_oddBoundary _ v).mp hv
  rw [incidentCount_add, incidentCount_singleton] at ho
  simp only [pairInc, if_neg hP, add_zero] at he
  exact (Nat.not_even_iff_odd.mpr ho) he

theorem boundary_append_pair_weight {V : Type} [Fintype V] [DecidableEq V]
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (E : Multiset (Sym2 V)) (P Q : PairVertex V)
    (hp : ∀ v, Even (incidentCount E v + pairInc P v + pairInc Q v)) :
    (∑ v ∈ oddBoundary (E + {Q.val}), x v) ≤ pairWeight x P := by
  rw [pairWeight_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (boundary_append_pair_subset E P Q hp)
    (fun v _ _ => hx v)

theorem boundary_append_two_pairs {V : Type} [Fintype V] [DecidableEq V]
    (E : Multiset (Sym2 V)) (P Q : PairVertex V)
    (hp : ∀ v, Even (incidentCount E v + pairInc P v + pairInc Q v)) :
    oddBoundary (E + {P.val} + {Q.val}) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have ho := (mem_oddBoundary _ v).mp hv
  rw [incidentCount_add, incidentCount_add, incidentCount_singleton, incidentCount_singleton] at ho
  exact (Nat.not_even_iff_odd.mpr ho) (hp v)

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: PairFeasibility -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole

theorem pair_system_feasible {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (hodd : ∀ E : Multiset (Sym2 V), (∀ e ∈ E, e ∈ G.edgeSet) → Odd E.card →
      edgeWeightSum x E ≤ (E.card : ℝ) - 1 + ∑ v ∈ oddBoundary E, x v) :
    ∃ y : PairVertex V → ℝ,
      (∀ P Q, (pairGraph G).Adj P Q →
        pairLower x s(P,Q) ≤ y P + y Q ∧ y P + y Q ≤ pairUpper x s(P,Q)) ∧
      (∀ P, 0 ≤ y P) ∧ (∀ P ∈ forcedPairs G, y P = 0) := by
  classical
  apply aux_tvs_construct
  · intro p v hv hp
    obtain ⟨E, hcard, hE, hpar, hB, _⟩ := bracing_certificate G x p v hv
    have ho : Odd E.card := by rw [hcard]; exact hp
    have hb := hodd E hE ho
    have he := boundary_weight_le_pairs x hx E (v 0) (v (Fin.last p)) hpar
    rw [hcard] at hb
    have hne : ¬ Even p := Nat.not_even_iff_odd.mpr hp
    simp only [hne, ite_false, neg_one_mul, sub_neg_eq_add] at hB
    nlinarith
  · intro p v hv hp hlast
    obtain ⟨E, hcard, hE, hpar, hB, _⟩ := bracing_certificate G x p v hv
    have hGlast : (v (Fin.last p)).val ∈ G.edgeSet := (mem_forcedPairs G _).mp hlast
    have hsupport : ∀ e ∈ E + {(v (Fin.last p)).val}, e ∈ G.edgeSet := by
      intro e he
      rcases Multiset.mem_add.mp he with he | he
      · exact hE e he
      · simpa only [Multiset.mem_singleton.mp he] using hGlast
    have ho : Odd (E + {(v (Fin.last p)).val}).card := by
      simpa only [Multiset.card_add, Multiset.card_singleton, hcard] using hp.add_one
    have hb := hodd _ hsupport ho
    have he := boundary_append_pair_weight x hx E (v 0) (v (Fin.last p)) hpar
    have hw : edgeWeightSum x (E + {(v (Fin.last p)).val}) =
        edgeWeightSum x E + pairWeight x (v (Fin.last p)) := by
      simp [edgeWeightSum, pairWeight]
    rw [hw, Multiset.card_add, Multiset.card_singleton, hcard, Nat.cast_add, Nat.cast_one] at hb
    simp only [hp, ite_true, sub_zero, one_mul] at hB
    nlinarith
  · intro p v hv hp hfirst hlast
    obtain ⟨E, hcard, hE, hpar, _, hA⟩ := bracing_certificate G x p v hv
    have hGfirst : (v 0).val ∈ G.edgeSet := (mem_forcedPairs G _).mp hfirst
    have hGlast : (v (Fin.last p)).val ∈ G.edgeSet := (mem_forcedPairs G _).mp hlast
    have hsupport : ∀ e ∈ E + {(v 0).val} + {(v (Fin.last p)).val}, e ∈ G.edgeSet := by
      intro e he
      rcases Multiset.mem_add.mp he with he | he
      · rcases Multiset.mem_add.mp he with he | he
        · exact hE e he
        · simpa only [Multiset.mem_singleton.mp he] using hGfirst
      · simpa only [Multiset.mem_singleton.mp he] using hGlast
    have ho : Odd (E + {(v 0).val} + {(v (Fin.last p)).val}).card := by
      rw [Multiset.card_add, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_singleton, hcard]
      simpa only [Nat.add_assoc] using hp.add_even (show Even (1+1) by decide)
    have hb := hodd _ hsupport ho
    have hboundary := boundary_append_two_pairs E (v 0) (v (Fin.last p)) hpar
    have hw : edgeWeightSum x (E + {(v 0).val} + {(v (Fin.last p)).val}) =
        edgeWeightSum x E + pairWeight x (v 0) + pairWeight x (v (Fin.last p)) := by
      simp [edgeWeightSum, pairWeight]
    rw [hw, hboundary, Finset.sum_empty, add_zero, Multiset.card_add,
      Multiset.card_add, Multiset.card_singleton, Multiset.card_singleton, hcard,
      Nat.cast_add, Nat.cast_add, Nat.cast_one] at hb
    have hne : ¬ Even p := Nat.not_even_iff_odd.mpr hp
    simp only [hne, ite_false, neg_one_mul] at hA
    nlinarith

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: MatrixSystem -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole Matrix

theorem mem_NG_of_matrix_system {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (x : V → ℝ)
    (hx : x ∈ FRAC G) (Y : Matrix (Option V) (Option V) ℝ)
    (hpos : ∀ p q, 0 ≤ Y p q) (hsymm : Y.IsSymm) (h00 : Y none none = 1)
    (hdiag : ∀ i, Y (some i) none = x i ∧ Y (some i) (some i) = x i)
    (hsys : ∀ i j k, G.Adj i j →
      x i + x j + x k - 1 ≤ Y (some i) (some k) + Y (some j) (some k) ∧
      Y (some i) (some k) + Y (some j) (some k) ≤ x k) : x ∈ NG G := by
  have h0i (i : V) : Y none (some i) = x i := by
    rw [← hsymm.apply none (some i)]
    exact (hdiag i).1
  have hproj : Y.mulVec (Pi.single none 1) = hom x := by
    rw [Matrix.mulVec_single_one]
    funext o
    cases o with
    | none => exact h00
    | some i => exact (hdiag i).1
  have hi (k : V) : Y.mulVec (Pi.single (some k) 1) ∈ FR G := by
    rw [Matrix.mulVec_single_one]
    refine ⟨fun i => hpos (some i) (some k), ?_⟩
    intro i j hij
    change Y (some i) (some k) + Y (some j) (some k) ≤ Y none (some k)
    rw [h0i]
    exact (hsys i j k hij).2
  have hc (k : V) : Y.mulVec (Pi.single none 1 - Pi.single (some k) 1) ∈ FR G := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    constructor
    · intro i
      obtain ⟨j, hkj⟩ := hG k
      have hh := (hsys k j i hkj).2
      have hn := hpos (some j) (some i)
      have he : Y (some k) (some i) = Y (some i) (some k) := hsymm.apply (some i) (some k)
      change 0 ≤ Y (some i) none - Y (some i) (some k)
      rw [(hdiag i).1]
      linarith
    · intro i j hij
      have hh := (hsys i j k hij).1
      change (Y (some i) none - Y (some i) (some k)) +
        (Y (some j) none - Y (some j) (some k)) ≤ Y none none - Y none (some k)
      rw [(hdiag i).1, (hdiag j).1, h00, h0i]
      linarith
  refine ⟨Y, matrix_mem_of_columns G Y hsymm ?_ ?_ hi hc, hproj⟩
  · intro i
    rw [(hdiag i).2, h0i]
  · rw [hproj]
    exact hx

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: PairLift -/
section

namespace LovaszSchrijver.OddHoleProof
open LovaszSchrijver.OddHole Matrix

def pairMatrix {V : Type} [DecidableEq V] (x : V → ℝ) (y : PairVertex V → ℝ) :
    Matrix (Option V) (Option V) ℝ
  | none, none => 1
  | none, some j => x j
  | some i, none => x i
  | some i, some j => if h : i = j then x i else y (mkPair i j h)

@[simp] theorem pairMatrix_diag {V : Type} [DecidableEq V]
    (x : V → ℝ) (y : PairVertex V → ℝ) (i : V) :
    pairMatrix x y (some i) (some i) = x i := by simp [pairMatrix]

theorem pairMatrix_offdiag {V : Type} [DecidableEq V]
    (x : V → ℝ) (y : PairVertex V → ℝ) {i j : V} (hij : i ≠ j) :
    pairMatrix x y (some i) (some j) = y (mkPair i j hij) := by simp [pairMatrix, hij]

theorem pairMatrix_symm {V : Type} [DecidableEq V]
    (x : V → ℝ) (y : PairVertex V → ℝ) : (pairMatrix x y).IsSymm := by
  apply Matrix.IsSymm.ext
  intro p q
  cases p with
  | none => cases q <;> rfl
  | some i =>
    cases q with
    | none => rfl
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · rw [pairMatrix_offdiag x y (Ne.symm hij), pairMatrix_offdiag x y hij]
        congr 1
        apply Subtype.ext
        exact Sym2.eq_swap

theorem pairMatrix_edge_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V → ℝ) (y : PairVertex V → ℝ)
    (hy : ∀ P ∈ forcedPairs G, y P = 0) {i j : V} (hij : G.Adj i j) :
    pairMatrix x y (some i) (some j) = 0 := by
  rw [pairMatrix_offdiag x y hij.ne]
  exact hy _ ((mem_forcedPairs G _).mpr hij)

theorem mem_NG_of_pair_solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (x : V → ℝ) (hx : x ∈ FRAC G)
    (y : PairVertex V → ℝ)
    (hsys : ∀ P Q, (pairGraph G).Adj P Q →
      pairLower x s(P,Q) ≤ y P + y Q ∧ y P + y Q ≤ pairUpper x s(P,Q))
    (hpos : ∀ P, 0 ≤ y P) (hzero : ∀ P ∈ forcedPairs G, y P = 0) : x ∈ NG G := by
  refine mem_NG_of_matrix_system G hG x hx (pairMatrix x y) ?_ (pairMatrix_symm x y)
    rfl (fun i => ⟨rfl, pairMatrix_diag x y i⟩) ?_
  · intro p q
    cases p with
    | none =>
      cases q with
      | none => exact zero_le_one
      | some j => exact hx.1 j
    | some i =>
      cases q with
      | none => exact hx.1 i
      | some j =>
        by_cases hij : i = j
        · subst j
          rw [pairMatrix_diag]
          exact hx.1 i
        · rw [pairMatrix_offdiag x y hij]
          exact hpos _
  · intro i j k hij
    by_cases hki : k = i
    · subst k
      rw [pairMatrix_diag, pairMatrix_edge_zero G x y hzero hij.symm, add_zero]
      exact ⟨by linarith [hx.2 i j hij], le_rfl⟩
    · by_cases hkj : k = j
      · subst k
        rw [pairMatrix_edge_zero G x y hzero hij, pairMatrix_diag, zero_add]
        exact ⟨by linarith [hx.2 i j hij], le_rfl⟩
      · have hAdj : (pairGraph G).Adj (mkPair i k (Ne.symm hki)) (mkPair j k (Ne.symm hkj)) :=
          ⟨i,j,k,hij,rfl,rfl⟩
        have hh := hsys _ _ hAdj
        have hb := pair_bounds_witness x (P := mkPair i k (Ne.symm hki))
          (Q := mkPair j k (Ne.symm hkj)) hij.ne rfl rfl
        rw [hb.2, hb.1] at hh
        rw [pairMatrix_offdiag x y (Ne.symm hki), pairMatrix_offdiag x y (Ne.symm hkj)]
        exact hh

theorem mem_NG_of_odd_edge_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (x : V → ℝ) (hx : x ∈ FRAC G)
    (hodd : ∀ E : Multiset (Sym2 V), (∀ e ∈ E, e ∈ G.edgeSet) → Odd E.card →
      edgeWeightSum x E ≤ (E.card : ℝ) - 1 + ∑ v ∈ oddBoundary E, x v) : x ∈ NG G := by
  obtain ⟨y, hsys, hpos, hzero⟩ := pair_system_feasible G x hx.1 hodd
  exact mem_NG_of_pair_solution G hG x hx y hsys hpos hzero

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: CycleVertices -/
section

set_option autoImplicit false
open LovaszSchrijver.OddHole

namespace LovaszSchrijver.OddHoleProof

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

def cycleVertex {u : V} (p : G.Walk u u) (i : Fin p.length) : V := p.getVert i.val

def cycleVertices {u : V} (p : G.Walk u u) : Finset V := p.support.dropLast.toFinset

def cyclicNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩

omit [DecidableEq V] in
theorem dropLast_support_ofFn {u : V} (p : G.Walk u u) :
    p.support.dropLast = List.ofFn (cycleVertex p) := by
  apply List.ext_getElem
  · simp [SimpleGraph.Walk.length_support]
  · intro i hi hj
    have hil : i ≤ p.length := by
      simp only [List.length_dropLast, SimpleGraph.Walk.length_support] at hi
      omega
    simp only [List.getElem_dropLast, List.getElem_ofFn, cycleVertex]
    exact (p.getVert_eq_support_getElem hil).symm

theorem cycleVertices_eq_image {u : V} (p : G.Walk u u) :
    cycleVertices p = Finset.univ.image (cycleVertex p) := by
  rw [cycleVertices, dropLast_support_ofFn]
  ext v
  simp

omit [DecidableEq V] in
theorem cycleVertex_injective {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    Function.Injective (cycleVertex p) := by
  intro i j hij
  apply Fin.ext
  exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hij

theorem cycleVertices_card {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    (cycleVertices p).card = p.length := by
  rw [cycleVertices, List.toFinset_card_of_nodup hp.nodup_dropLast_support]
  simp [SimpleGraph.Walk.length_support]

omit [DecidableEq V] in
theorem cycleVertex_next {u : V} (p : G.Walk u u) (hn : 0 < p.length)
    (i : Fin p.length) : p.getVert (i.val+1) = cycleVertex p (cyclicNext hn i) := by
  by_cases hi : i.val+1 < p.length
  · simp [cycleVertex, cyclicNext, Nat.mod_eq_of_lt hi]
  · have he : i.val+1 = p.length := by omega
    simp [cycleVertex, cyclicNext, he]

omit [DecidableEq V] in
theorem cycle_edge_iff {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    (i j : Fin p.length) :
    s(cycleVertex p i,cycleVertex p j) ∈ p.edges ↔
      j.val = (i.val+1)%p.length ∨ i.val = (j.val+1)%p.length := by
  have hn : 0 < p.length := lt_of_lt_of_le (by norm_num : 0 < 3) hp.three_le_length
  have hinj := cycleVertex_injective hp
  rw [p.mk_mem_edges_iff_exists]
  constructor
  · rintro ⟨k,hk,he⟩
    let K : Fin p.length := ⟨k,hk⟩
    have hh : s(cycleVertex p K,cycleVertex p (cyclicNext hn K)) =
        s(cycleVertex p i,cycleVertex p j) := by
      rw [← cycleVertex_next]
      exact he
    rcases Sym2.eq_iff.mp hh with ⟨hki,hnj⟩ | ⟨hkj,hni⟩
    · have h₁ := hinj hki
      have h₂ := hinj hnj
      left
      rw [← h₁, ← h₂]
      rfl
    · have h₁ := hinj hkj
      have h₂ := hinj hni
      right
      rw [← h₁, ← h₂]
      rfl
  · rintro (h | h)
    · have he : cyclicNext hn i = j := Fin.ext h.symm
      refine ⟨i.val,i.isLt,?_⟩
      rw [cycleVertex_next p hn i, he]
      rfl
    · have he : cyclicNext hn j = i := Fin.ext h.symm
      refine ⟨j.val,j.isLt,?_⟩
      rw [cycleVertex_next p hn j, he]
      exact Sym2.eq_swap

theorem chordless_cycle_isOddHole {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    (hodd : Odd p.length)
    (hchordless : ∀ a ∈ p.support, ∀ b ∈ p.support,
      G.Adj a b → s(a,b) ∈ p.edges) : IsOddHole G (cycleVertices p) := by
  let f : Fin p.length → cycleVertices p := fun i => ⟨cycleVertex p i, by
    rw [cycleVertices_eq_image]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      exact cycleVertex_injective hp (congrArg Subtype.val he)
    · rintro ⟨v,hv⟩
      rw [cycleVertices_eq_image] at hv
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
      exact ⟨i,Subtype.ext hi⟩
  let e : Fin p.length ≃ cycleVertices p := Equiv.ofBijective f hf
  refine ⟨p.length,hodd,hp.three_le_length,e,?_⟩
  intro i j
  change G.Adj (cycleVertex p i) (cycleVertex p j) ↔ _
  rw [← cycle_edge_iff hp]
  constructor
  · exact hchordless _ (p.getVert_mem_support _) _ (p.getVert_mem_support _)
  · intro he
    exact p.edges_subset_edgeSet he

omit [DecidableEq V] in
theorem walkWeight_support (x : V → ℝ) {u v : V} (p : G.Walk u v) :
    walkWeight x p = 2*(p.support.map x).sum-x u-x v := by
  induction p with
  | nil => simp; ring
  | cons h p ih =>
    simp only [walkWeight_cons, SimpleGraph.Walk.support_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem cycle_weight_sum (x : V → ℝ) {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    walkWeight x p = 2*∑ v ∈ cycleVertices p, x v := by
  rw [walkWeight_support, ← p.cons_tail_support]
  simp only [List.map_cons, List.sum_cons]
  have hs := ((p.tail_support_perm_dropLast_support).map x).sum_eq
  rw [hs, ← List.sum_toFinset x hp.nodup_dropLast_support]
  change 2*(x u + ∑ v ∈ cycleVertices p,x v)-x u-x u = _
  ring

theorem chordless_cycle_weight_le (x : V → ℝ)
    (hx : ∀ C : Finset V, IsOddHole G C → ∑ v ∈ C,x v ≤ ((C.card:ℝ)-1)/2)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) (hodd : Odd p.length)
    (hchordless : ∀ a ∈ p.support, ∀ b ∈ p.support,G.Adj a b → s(a,b) ∈ p.edges) :
    walkWeight x p ≤ (p.length:ℝ)-1 := by
  have h := hx (cycleVertices p) (chordless_cycle_isOddHole hp hodd hchordless)
  rw [cycleVertices_card hp] at h
  rw [cycle_weight_sum x hp]
  linarith

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: OddWalkWeights -/
section

set_option autoImplicit false
namespace LovaszSchrijver.OddHoleProof
variable {V : Type*}

theorem odd_length_walkWeight_le (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ u v, G.Adj u v → x u+x v ≤ 1) (k : ℕ) :
    ∀ {u v : V} (p : G.Walk u v), p.length = 2*k+1 →
      walkWeight x p ≤ (2*k : ℝ)+x u+x v := by
  induction k with
  | zero =>
    intro u v p hlen
    cases p with
    | nil => simp at hlen
    | @cons u w v huv q =>
      cases q with
      | nil => simp
      | cons hwz r =>
        simp only [SimpleGraph.Walk.length_cons] at hlen
        omega
  | succ k ih =>
    intro u v p hlen
    cases p with
    | nil => simp only [SimpleGraph.Walk.length_nil] at hlen; omega
    | @cons u w v huv q =>
      cases q with
      | nil => simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen; omega
      | @cons w z v hwz r =>
        have hr : r.length = 2*k+1 := by
          simp only [SimpleGraph.Walk.length_cons] at hlen
          omega
        have hh := ih r hr
        have he := hx w z hwz
        simp only [walkWeight_cons, Nat.cast_add, Nat.cast_one]
        linarith

theorem odd_walkWeight_le (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ u v, G.Adj u v → x u+x v ≤ 1) {u v : V}
    (p : G.Walk u v) (hp : Odd p.length) :
    walkWeight x p ≤ (p.length : ℝ)-1+x u+x v := by
  obtain ⟨k,hk⟩ := hp
  have hk' : p.length = 2*k+1 := by omega
  have h := odd_length_walkWeight_le G x hx k p hk'
  rw [hk']
  push_cast
  linarith

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: ClosedTrails -/
section

set_option autoImplicit false

namespace LovaszSchrijver.OddHoleProof

variable {V : Type*} {G : SimpleGraph V}

/-- Removing an even cycle reduces the remaining odd closed trail. -/
theorem odd_closedTrail_weight_of_cycles_bounded (x : V → ℝ)
    (hxe : ∀ u v, G.Adj u v → x u+x v ≤ 1) (N : ℕ)
    (hcycle : ∀ {u : V} (c : G.Walk u u), c.IsCycle → Odd c.length → c.length ≤ N →
      walkWeight x c ≤ (c.length : ℝ)-1)
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) (hodd : Odd p.length) (hpN : p.length ≤ N) :
    walkWeight x p ≤ (p.length : ℝ)-1 := by
  classical
  have hn : ¬p.IsPath := by
    intro h
    have hz := SimpleGraph.Walk.isPath_iff_nil.mp h
    have : p.length = 0 := hz.length_eq_zero
    simp [this] at hodd
  have hex : ∃ (v : V) (c : G.Walk v v), c.IsSubwalk p ∧ c.IsCycle := by
    by_contra he
    push Not at he
    exact hn (hp.isPath_iff_isSubwalk_imp_not_isCycle.mpr he)
  obtain ⟨v,c,hsub,hc⟩ := hex
  obtain ⟨l,r,hdecomp⟩ := hsub
  have hlen : p.length = l.length+c.length+r.length := by
    rw [hdecomp]; simp only [SimpleGraph.Walk.length_append]
  have hw : walkWeight x p = walkWeight x l+walkWeight x c+walkWeight x r := by
    rw [hdecomp]; simp only [walkWeight_append]
  by_cases ho : Odd c.length
  · have hcW := hcycle c hc ho ((SimpleGraph.Walk.length_le_of_isSubwalk ⟨l,r,hdecomp⟩).trans hpN)
    have hlW := walkWeight_le_length G x hxe l
    have hrW := walkWeight_le_length G x hxe r
    rw [hw, hlen]
    push_cast
    linarith
  · have hrest : (l.append r).IsTrail := by
      constructor
      refine List.Nodup.sublist ?_ hp.edges_nodup
      rw [hdecomp]
      simp only [SimpleGraph.Walk.edges_append]
      exact (List.sublist_append_left _ _).append (List.Sublist.refl _)
    have hrestodd : Odd (l.append r).length := by
      simp only [SimpleGraph.Walk.length_append]
      rw [hlen] at hodd
      simp only [Nat.odd_iff] at ho hodd ⊢
      omega
    have hlt : (l.append r).length < p.length := by
      have := hc.three_le_length
      simp only [SimpleGraph.Walk.length_append]
      omega
    have hi := odd_closedTrail_weight_of_cycles_bounded x hxe N hcycle (l.append r) hrest hrestodd (hlt.le.trans hpN)
    have hcW := walkWeight_le_length G x hxe c
    rw [walkWeight_append] at hi
    simp only [SimpleGraph.Walk.length_append, Nat.cast_add] at hi
    rw [hw, hlen]
    push_cast
    linarith
termination_by p.length
decreasing_by exact hlt

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: ChordReduction -/
section

set_option autoImplicit false

namespace LovaszSchrijver.OddHoleProof

variable {V : Type*} {G : SimpleGraph V}

/-- A fresh chord and an odd complementary arc reduce the closed-trail estimate. -/
theorem chord_pair_weight_bound (x : V → ℝ)
    (hxe : ∀ u v, G.Adj u v → x u+x v ≤ 1)
    {u v : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsTrail) (hq : q.IsTrail) (hch : G.Adj u v)
    (hfp : s(u,v) ∉ p.edges) (hfq : s(u,v) ∉ q.edges)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hodd : Odd (p.length+q.length))
    (hsmall : ∀ {w : V} (c : G.Walk w w), c.IsTrail → Odd c.length →
      c.length < p.length+q.length → walkWeight x c ≤ (c.length : ℝ)-1) :
    walkWeight x p+walkWeight x q ≤ ((p.length+q.length : ℕ) : ℝ)-1 := by
  rcases Nat.even_or_odd p.length with hpEven | hpOdd
  · have hqOdd : Odd q.length := by
      simp only [Nat.even_iff, Nat.odd_iff] at hpEven hodd ⊢
      omega
    have hc : (SimpleGraph.Walk.cons hch.symm p).IsTrail :=
      (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hp, by simpa only [Sym2.eq_swap] using hfp⟩
    have hcOdd : Odd (SimpleGraph.Walk.cons hch.symm p).length := by
      simpa only [SimpleGraph.Walk.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even] using hpEven
    have hcLen : (SimpleGraph.Walk.cons hch.symm p).length < p.length+q.length := by
      simp only [SimpleGraph.Walk.length_cons]
      omega
    have hcW := hsmall _ hc hcOdd hcLen
    have hqW := odd_walkWeight_le G x hxe q hqOdd
    simp only [walkWeight_cons, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at hcW
    push_cast
    linarith
  · have hqEven : Even q.length := by
      simp only [Nat.even_iff, Nat.odd_iff] at hpOdd hodd ⊢
      omega
    have hc : (SimpleGraph.Walk.cons hch q).IsTrail :=
      (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hq, hfq⟩
    have hcOdd : Odd (SimpleGraph.Walk.cons hch q).length := by
      simpa only [SimpleGraph.Walk.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even] using hqEven
    have hcLen : (SimpleGraph.Walk.cons hch q).length < p.length+q.length := by
      simp only [SimpleGraph.Walk.length_cons]
      omega
    have hcW := hsmall _ hc hcOdd hcLen
    have hpW := odd_walkWeight_le G x hxe p hpOdd
    simp only [walkWeight_cons, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at hcW
    push_cast
    linarith

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: OddCycleWeights -/
section

set_option autoImplicit false
open LovaszSchrijver.OddHole

namespace LovaszSchrijver.OddHoleProof

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem fresh_endpoint_edge_length {u v : V} (p : G.Walk u v) (hne : u ≠ v)
    (hfresh : s(u,v) ∉ p.edges) : 2 ≤ p.length := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons h q =>
    cases q with
    | nil => simp at hfresh
    | cons h' r => simp only [SimpleGraph.Walk.length_cons]; omega

theorem walkWeight_rotate (x : V → ℝ) {u v : V} (p : G.Walk u u)
    (hv : v ∈ p.support) : walkWeight x (p.rotate v hv) = walkWeight x p := by
  have h := ((p.rotate_edges v hv).perm.map (edgeWeight x)).sum_eq
  simpa [walkWeight, edgeWeightSum] using h

theorem odd_cycle_weight_le (x : V → ℝ)
    (hxe : ∀ u v, G.Adj u v → x u+x v ≤ 1)
    (hoddHole : ∀ C : Finset V, IsOddHole G C → ∑ v ∈ C,x v ≤ ((C.card:ℝ)-1)/2)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) (hodd : Odd p.length) :
    walkWeight x p ≤ (p.length:ℝ)-1 := by
  classical
  have bound : ∀ n : ℕ, ∀ {u : V} (p : G.Walk u u), p.length=n → p.IsCycle → Odd n →
      walkWeight x p ≤ (n:ℝ)-1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u p hlen hp hodd
      have hoddp : Odd p.length := by rwa [hlen]
      by_cases hch : ∀ a ∈ p.support, ∀ b ∈ p.support, G.Adj a b → s(a,b) ∈ p.edges
      · simpa only [hlen] using chordless_cycle_weight_le x hoddHole hp hoddp hch
      · push Not at hch
        obtain ⟨a,ha,b,hb,hab,hfresh⟩ := hch
        let c := p.rotate a ha
        have hc : c.IsCycle := hp.rotate ha
        have hbc : b ∈ c.support := by simpa [c] using hb
        let l := c.takeUntil b hbc
        let r := c.dropUntil b hbc
        have hsplit : l.append r = c := c.take_spec hbc
        have hflen : l.length+r.length = n := by
          have hh := congrArg SimpleGraph.Walk.length hsplit
          simpa only [SimpleGraph.Walk.length_append, c, SimpleGraph.Walk.length_rotate, hlen] using hh
        have hf : s(a,b) ∉ c.edges := by
          intro he
          exact hfresh ((p.rotate_edges a ha).perm.mem_iff.mp he)
        have hfl : s(a,b) ∉ l.edges := fun he => hf (c.edges_takeUntil_subset_edges hbc he)
        have hfr : s(a,b) ∉ r.edges := fun he => hf (c.edges_dropUntil_subset_edges hbc he)
        have hl2 : 2 ≤ l.length := fresh_endpoint_edge_length l hab.ne hfl
        have hr2 : 2 ≤ r.length := fresh_endpoint_edge_length r hab.ne.symm (by
          simpa only [Sym2.eq_swap] using hfr)
        have hsmall : ∀ {w : V} (q : G.Walk w w), q.IsTrail → Odd q.length →
            q.length < l.length+r.length → walkWeight x q ≤ (q.length:ℝ)-1 := by
          intro w q hqt hqo hql
          apply odd_closedTrail_weight_of_cycles_bounded x hxe q.length
            (fun {_} z hzc hzo hzl => ih z.length (hzl.trans_lt (hflen ▸ hql)) z rfl hzc hzo)
            q hqt hqo le_rfl
        have hw := chord_pair_weight_bound x hxe l r (hc.isTrail.takeUntil hbc)
          (hc.isTrail.dropUntil hbc) hab hfl hfr hl2 hr2 (by rwa [hflen]) hsmall
        rw [← walkWeight_append, hsplit, walkWeight_rotate, hflen] at hw
        exact hw
  exact bound p.length p rfl hp hodd

theorem odd_closedTrail_weight_le (x : V → ℝ)
    (hxe : ∀ u v, G.Adj u v → x u+x v ≤ 1)
    (hoddHole : ∀ C : Finset V, IsOddHole G C → ∑ v ∈ C,x v ≤ ((C.card:ℝ)-1)/2)
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) (hodd : Odd p.length) :
    walkWeight x p ≤ (p.length:ℝ)-1 :=
  odd_closedTrail_weight_of_cycles_bounded x hxe p.length
    (fun {_} c hc ho _ => odd_cycle_weight_le x hxe hoddHole c hc ho) p hp hodd le_rfl

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: TrailBoundary -/
section

set_option autoImplicit false
open scoped symmDiff

namespace LovaszSchrijver.OddHoleProof

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem oddBoundary_add (E F : Multiset (Sym2 V)) :
    oddBoundary (E+F) = oddBoundary E ∆ oddBoundary F := by
  ext v
  simp only [mem_oddBoundary, Finset.mem_symmDiff, incidentCount_add, Nat.odd_iff]
  omega

theorem oddBoundary_cons_cons (e : Sym2 V) (E : Multiset (Sym2 V)) :
    oddBoundary (e ::ₘ e ::ₘ E) = oddBoundary E := by
  ext v
  simp only [mem_oddBoundary, incidentCount_cons, Nat.odd_iff]
  split_ifs <;> omega

theorem mem_oddBoundary_trail {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsTrail) (z : V) :
    z ∈ oddBoundary (p.edges : Multiset (Sym2 V)) ↔ u ≠ v ∧ (z=u ∨ z=v) := by
  rw [mem_oddBoundary]
  change Odd (p.edges.countP (fun e => z ∈ e)) ↔ _
  rw [← Nat.not_even_iff_odd, hp.even_countP_edges_iff z]
  tauto

theorem oddBoundary_sub_subset {E T : Multiset (Sym2 V)} (hT : T ≤ E)
    (hb : oddBoundary T ⊆ oddBoundary E) : oddBoundary (E-T) ⊆ oddBoundary E := by
  intro v hv
  by_contra hnot
  have ht : v ∉ oddBoundary T := fun h => hnot (hb h)
  have he := congrArg (fun E => incidentCount E v) (add_tsub_cancel_of_le hT)
  rw [incidentCount_add] at he
  simp only [mem_oddBoundary, Nat.odd_iff] at hv hnot ht
  omega

omit [Fintype V] in
/-- Maximality makes every edge incident to the initial vertex part of the trail. -/
theorem maximalTrail_incident_left (G : SimpleGraph V) {u v : V} (p : G.Walk u v)
    (hp : p.IsTrail)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → q.length ≤ p.length) :
    ∀ e ∈ G.edgeSet, u ∈ e → e ∈ p.edges := by
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he hu
    have hab : G.Adj a b := he
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · by_contra hn
      have ht : (SimpleGraph.Walk.cons hab.symm p).IsTrail :=
        (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hp, by simpa only [Sym2.eq_swap] using hn⟩
      have hlen := hmax _ _ _ ht
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    · by_contra hn
      have ht : (SimpleGraph.Walk.cons hab p).IsTrail :=
        (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hp, hn⟩
      have hlen := hmax _ _ _ ht
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: RestrictedTrails -/
section

set_option autoImplicit false

namespace LovaszSchrijver.OddHoleProof

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Finite edge support gives a longest admissible trail without an Eulerian-existence theorem. -/
theorem exists_restricted_maximal_trail [Nonempty V] (G : SimpleGraph V)
    (E : Multiset (Sym2 V)) :
    ∃ (u v : V) (p : G.Walk u v) (_hp : p.IsTrail),
      (∀ e ∈ p.edges,e ∈ E) ∧
      ∀ (a b : V) (q : G.Walk a b), q.IsTrail → (∀ e ∈ q.edges,e ∈ E) →
        q.length ≤ p.length := by
  classical
  let S : Set ℕ := {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧
    (∀ e ∈ p.edges,e ∈ E) ∧ p.length=n}
  have hfinite : S.Finite := (Set.finite_le_nat E.card).subset (by
    rintro n ⟨u,v,p,hp,hs,rfl⟩
    have hle : (p.edges : Multiset (Sym2 V)) ≤ E :=
      (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hp.edges_nodup)).mpr (fun e he => hs e (Multiset.mem_coe.mp he))
    have hc := Multiset.card_le_card hle
    change p.length ≤ E.card
    simpa only [Multiset.coe_card, SimpleGraph.Walk.length_edges] using hc)
  obtain ⟨u⟩ := ‹Nonempty V›
  have hne : S.Nonempty := ⟨0,u,u,.nil,by simp,by simp,rfl⟩
  obtain ⟨n,⟨⟨u,v,p,hp,hs,hn⟩,hmax⟩⟩ := hfinite.exists_maximal hne
  refine ⟨u,v,p,hp,hs,?_⟩
  intro a b q hq hqs
  have h := hmax ⟨a,b,q,hq,hqs,rfl⟩
  omega

theorem restricted_maximal_incident_left (G : SimpleGraph V) (E : Multiset (Sym2 V))
    (hE : ∀ e ∈ E,e ∈ G.edgeSet)
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (hs : ∀ e ∈ p.edges,e ∈ E)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → (∀ e ∈ q.edges,e ∈ E) →
      q.length ≤ p.length) : ∀ e ∈ E,u ∈ e → e ∈ p.edges := by
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he hu
    have hab : G.Adj a b := hE _ he
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · by_contra hn
      have ht : (SimpleGraph.Walk.cons hab.symm p).IsTrail :=
        (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hp,by simpa only [Sym2.eq_swap] using hn⟩
      have hsub : ∀ e ∈ (SimpleGraph.Walk.cons hab.symm p).edges,e ∈ E := by
        intro e he'
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he'
        rcases he' with rfl | he'
        · simpa only [Sym2.eq_swap] using he
        · exact hs e he'
      have hlen := hmax _ _ _ ht hsub
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    · by_contra hn
      have ht : (SimpleGraph.Walk.cons hab p).IsTrail :=
        (SimpleGraph.Walk.isTrail_cons _ _).mpr ⟨hp,hn⟩
      have hsub : ∀ e ∈ (SimpleGraph.Walk.cons hab p).edges,e ∈ E := by
        intro e he'
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact he
        · exact hs e he'
      have hlen := hmax _ _ _ ht hsub
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega

theorem incidentCount_eq_of_cover (E T : Multiset (Sym2 V)) (hE : E.Nodup) (hT : T.Nodup)
    (hTE : T ≤ E) (v : V) (hcover : ∀ e ∈ E,v ∈ e → e ∈ T) :
    incidentCount T v = incidentCount E v := by
  unfold incidentCount
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  congr 1
  apply (Multiset.Nodup.ext (hT.filter _) (hE.filter _)).mpr
  intro e
  simp only [Multiset.mem_filter]
  exact ⟨fun h => ⟨Multiset.mem_of_le hTE h.1,h.2⟩,
    fun h => ⟨hcover e h.1 h.2,h.2⟩⟩

omit [DecidableEq V] in
theorem restricted_maximal_length_pos (G : SimpleGraph V) (E : Multiset (Sym2 V))
    (hE : ∀ e ∈ E,e ∈ G.edgeSet) (hne : E ≠ 0)
    {u v : V} (p : G.Walk u v)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → (∀ e ∈ q.edges,e ∈ E) →
      q.length ≤ p.length) : 0 < p.length := by
  obtain ⟨e,he⟩ := Multiset.exists_mem_of_ne_zero hne
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := hE _ he
    have h := hmax a b hab.toWalk (by simp) (by
      intro e he'
      have heq : e = s(a,b) := by simpa using he'
      subst e
      exact he)
    have hlen : 1 ≤ p.length := by simpa using h
    omega

variable [Fintype V]

theorem restricted_maximal_boundary_subset (G : SimpleGraph V) (E : Multiset (Sym2 V))
    (hE : ∀ e ∈ E,e ∈ G.edgeSet) (hEN : E.Nodup)
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (hs : ∀ e ∈ p.edges,e ∈ E)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → (∀ e ∈ q.edges,e ∈ E) →
      q.length ≤ p.length) : oddBoundary (p.edges : Multiset (Sym2 V)) ⊆ oddBoundary E := by
  have hTE : (p.edges : Multiset (Sym2 V)) ≤ E :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hp.edges_nodup)).mpr (fun e he => hs e (Multiset.mem_coe.mp he))
  have hleft := restricted_maximal_incident_left G E hE p hp hs hmax
  have hright : ∀ e ∈ E,v ∈ e → e ∈ p.edges := by
    have hrev : p.reverse.IsTrail := SimpleGraph.Walk.IsTrail.reverse p hp
    have hrs : ∀ e ∈ p.reverse.edges,e ∈ E := by simpa using hs
    have hrmax : ∀ (a b : V) (q : G.Walk a b), q.IsTrail → (∀ e ∈ q.edges,e ∈ E) →
        q.length ≤ p.reverse.length := by simpa using hmax
    simpa using restricted_maximal_incident_left G E hE p.reverse hrev hrs hrmax
  intro z hz
  have hpar := (mem_oddBoundary_trail p hp z).mp hz
  rw [mem_oddBoundary] at hz ⊢
  rcases hpar.2 with rfl | rfl
  · rwa [← incidentCount_eq_of_cover E (p.edges : Multiset (Sym2 V)) hEN (Multiset.coe_nodup.mpr hp.edges_nodup) hTE z
      (fun e he h => Multiset.mem_coe.mpr (hleft e he h))]
  · rwa [← incidentCount_eq_of_cover E (p.edges : Multiset (Sym2 V)) hEN (Multiset.coe_nodup.mpr hp.edges_nodup) hTE z
      (fun e he h => Multiset.mem_coe.mpr (hright e he h))]

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: OddEdgeWeights -/
section

set_option autoImplicit false
open LovaszSchrijver.OddHole

namespace LovaszSchrijver.OddHoleProof

variable {V : Type} [Fintype V] [DecidableEq V]

theorem odd_edge_weight_le (G : SimpleGraph V) (x : V → ℝ)
    (hx0 : ∀ v,0 ≤ x v)
    (hxe : ∀ u v,G.Adj u v → x u+x v ≤ 1)
    (hodd : ∀ C : Finset V,IsOddHole G C → ∑ v ∈ C,x v ≤ ((C.card:ℝ)-1)/2)
    (E : Multiset (Sym2 V)) (hE : ∀ e ∈ E,e ∈ G.edgeSet) (hcard : Odd E.card) :
    edgeWeightSum x E ≤ (E.card:ℝ)-1+∑ v ∈ oddBoundary E,x v := by
  classical
  have bound : ∀ n : ℕ, ∀ E : Multiset (Sym2 V), E.card=n →
      (∀ e ∈ E,e ∈ G.edgeSet) → Odd n →
        edgeWeightSum x E ≤ (n:ℝ)-1+∑ v ∈ oddBoundary E,x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E hEn hE hoddn
      by_cases hN : E.Nodup
      · have hnonzero : E ≠ 0 := by
          intro hz
          have : n = 0 := by simpa [hz] using hEn.symm
          simp [this] at hoddn
        obtain ⟨e,he⟩ := Multiset.exists_mem_of_ne_zero hnonzero
        have : Nonempty V := by
          induction e using Sym2.ind with
          | _ a b => exact ⟨a⟩
        obtain ⟨u,v,p,hp,hs,hmax⟩ := exists_restricted_maximal_trail G E
        let T : Multiset (Sym2 V) := p.edges
        let R := E-T
        have hTE : T ≤ E := (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hp.edges_nodup)).mpr
          (fun e he => hs e (Multiset.mem_coe.mp he))
        have hRE : ∀ e ∈ R,e ∈ G.edgeSet :=
          fun e he => hE e (Multiset.mem_of_le (tsub_le_self : R ≤ E) he)
        have hsum : T+R=E := add_tsub_cancel_of_le hTE
        have hlen : p.length+R.card=n := by
          have hh := congrArg Multiset.card hsum
          simpa only [Multiset.card_add, T, Multiset.coe_card,
            SimpleGraph.Walk.length_edges, hEn] using hh
        have hw : walkWeight x p+edgeWeightSum x R=edgeWeightSum x E := by
          simpa only [edgeWeightSum_add, walkWeight, T] using congrArg (edgeWeightSum x) hsum
        have hp0 := restricted_maximal_length_pos G E hE hnonzero p hmax
        have hb := restricted_maximal_boundary_subset G E hE hN p hp hs hmax
        by_cases hpOdd : Odd p.length
        · have hrest := edgeWeightSum_le_card G x hxe R hRE
          by_cases huv : u=v
          · subst v
            have hh := odd_closedTrail_weight_le x hxe hodd p hp hpOdd
            have hnn : 0 ≤ ∑ v ∈ oddBoundary E,x v := Finset.sum_nonneg (fun v _ => hx0 v)
            have hlen' : (p.length:ℝ)+(R.card:ℝ)=n := by exact_mod_cast hlen
            linarith
          · have hu : u ∈ oddBoundary E := hb ((mem_oddBoundary_trail p hp u).mpr
              ⟨huv,Or.inl rfl⟩)
            have hv : v ∈ oddBoundary E := hb ((mem_oddBoundary_trail p hp v).mpr
              ⟨huv,Or.inr rfl⟩)
            have hsub : ({u,v} : Finset V) ⊆ oddBoundary E := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hu
              · exact hv
            have hends : x u+x v ≤ ∑ v ∈ oddBoundary E,x v := by
              have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hx0 z)
              simpa [huv] using hh
            have hh := odd_walkWeight_le G x hxe p hpOdd
            have hlen' : (p.length:ℝ)+(R.card:ℝ)=n := by exact_mod_cast hlen
            linarith
        · have hRlt : R.card < n := by omega
          have hROdd : Odd R.card := by
            simp only [Nat.odd_iff] at hpOdd hoddn ⊢
            omega
          have hr := ih R.card hRlt R rfl hRE hROdd
          have hpW := walkWeight_le_length G x hxe p
          have hRsub : oddBoundary R ⊆ oddBoundary E := oddBoundary_sub_subset hTE hb
          have hbudget : (∑ v ∈ oddBoundary R,x v) ≤ ∑ v ∈ oddBoundary E,x v :=
            Finset.sum_le_sum_of_subset_of_nonneg hRsub (fun z _ _ => hx0 z)
          have hlen' : (p.length:ℝ)+(R.card:ℝ)=n := by exact_mod_cast hlen
          linarith
      · have hdup : ∃ e,1 < E.count e := by
          by_contra hh
          push Not at hh
          exact hN (Multiset.nodup_iff_count_le_one.mpr hh)
        obtain ⟨e,heCount⟩ := hdup
        have he : e ∈ E := Multiset.count_pos.mp (by omega)
        have he' : e ∈ E.erase e := by
          apply Multiset.count_pos.mp
          rw [Multiset.count_erase_self]
          omega
        let F := (E.erase e).erase e
        have heq : e ::ₘ e ::ₘ F=E := by
          change e ::ₘ e ::ₘ ((E.erase e).erase e)=E
          rw [Multiset.cons_erase he',Multiset.cons_erase he]
        have hFle : F ≤ E := (Multiset.erase_le _ _).trans (Multiset.erase_le _ _)
        have hFE : ∀ e ∈ F,e ∈ G.edgeSet := fun e he => hE e (Multiset.mem_of_le hFle he)
        have hlen : F.card+1+1=n := by
          have hh := congrArg Multiset.card heq
          simpa only [Multiset.card_cons,hEn] using hh
        have hFlt : F.card < n := by omega
        have hFOdd : Odd F.card := by
          simp only [Nat.odd_iff] at hoddn ⊢
          omega
        have hf := ih F.card hFlt F rfl hFE hFOdd
        have heW := edgeWeight_le_one G x hxe e (hE e he)
        have hlen' : (F.card:ℝ)+1+1=n := by exact_mod_cast hlen
        rw [← heq,edgeWeightSum_cons,edgeWeightSum_cons,oddBoundary_cons_cons]
        linarith
  exact bound E.card E rfl hE hcard

end LovaszSchrijver.OddHoleProof

end

/- Complete checked body: LovaszRoot -/
section

namespace LovaszSchrijver.OddHole
open LovaszSchrijver.OddHoleProof

theorem NG_eq_odd_hole_system {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    NG G = {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ (∀ i j, G.Adj i j → x i + x j ≤ 1) ∧
      ∀ C : Finset V, IsOddHole G C → ∑ i ∈ C, x i ≤ ((C.card : ℝ) - 1) / 2} := by
  ext x
  constructor
  · intro hx
    have hfrac := NG_subset_FRAC G hx
    exact ⟨hfrac.1, hfrac.2, fun C hC => odd_hole_valid_NG G hG x hx C hC⟩
  · rintro ⟨hx0, hxe, hodd⟩
    exact mem_NG_of_odd_edge_bound G hG x ⟨hx0, hxe⟩
      (fun E hE hcard => odd_edge_weight_le G x hx0 hxe hodd E hE hcard)

end LovaszSchrijver.OddHole

end

open LovaszSchrijver.OddHole

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    NG G = {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ (∀ i j, G.Adj i j → x i + x j ≤ 1) ∧
      ∀ C : Finset V, IsOddHole G C → ∑ i ∈ C, x i ≤ ((C.card : ℝ) - 1) / 2} := by
  exact LovaszSchrijver.OddHole.NG_eq_odd_hole_system G hG

#print axioms LovaszSchrijver.OddHole.NG_eq_odd_hole_system
#print axioms solution
