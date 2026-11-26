-- Prove2me | solution 1 for HMBinPacking.rational_strong_separation_answers
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:16:56.045875+00:00
-- url     : https://prove2.me/submissions/ae513e50-023c-4577-8849-f8ee2a73f575

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Theorems.Thm_HMBinPacking_cone_separation_from_one_residue_answer
import Mathlib.Algebra.BigOperators.Option
open HMBinPacking Finset

private lemma finite_config (I : Instance) (r : Fin I.d → Fin I.d) :
    (zCast '' Sr I r).Finite := by
  classical
  apply Set.Finite.image
  apply (Set.Finite.pi (t := fun _ : Fin I.d => Set.Icc (0:ℤ) (I.B:ℤ)) (fun _ => Set.finite_Icc _ _)).subset
  rintro v ⟨⟨hpos,hcap⟩,_⟩ i _
  have hh := Finset.single_le_sum (f := fun j => (I.s j:ℤ)*v j)
    (fun j (_ : j ∈ univ) => mul_nonneg (by positivity) (hpos j)) (Finset.mem_univ i)
  have hsi : (1:ℤ) ≤ I.s i := by exact_mod_cast I.s_pos i
  exact ⟨hpos i,le_trans (by simpa using mul_le_mul_of_nonneg_right hsi (hpos i)) (hh.trans hcap)⟩

private lemma finite_sep {n : ℕ} (s : Set (Fin n → ℝ)) (hs : s.Finite) (y : Fin n → ℚ) :
    ∃ w, IsSepAnswer (convexHull ℝ s) y w := by
  classical
  let Y := qCast y
  by_cases hy : Y ∈ convexHull ℝ s
  · exact ⟨_,Or.inl ⟨rfl,hy⟩⟩
  obtain ⟨f,b,hb,hyb⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ s) (hs.isClosed_convexHull ℝ) hy
  obtain ⟨a,hba,hay⟩ := exists_rat_btwn hyb
  let dot (v x : Fin n → ℝ) := ∑ i, v i * x i
  let c : Fin n → ℝ := fun i => f (Pi.single i 1)
  have fe (x : Fin n → ℝ) : dot c x = f x := by
    have e : x = ∑ i, x i • (Pi.single i 1 : Fin n → ℝ) := by
      ext j
      simp [Pi.smul_apply,Pi.single_apply,Finset.sum_apply,mul_ite]
    conv_rhs => rw [e]
    simp [dot,c,map_sum,mul_comm]
  let O : Set (Fin n → ℝ) := {v | (a:ℝ) < dot v Y} ∩ ⋂ x ∈ s, {v | dot v x < (a:ℝ)}
  have co (x : Fin n → ℝ) : Continuous (fun v => dot v x) := by
    dsimp [dot];fun_prop
  have ho : IsOpen O := (isOpen_lt continuous_const (co Y)).inter
    (hs.isOpen_biInter (fun x _ => isOpen_lt (co x) continuous_const))
  have hc : c ∈ O := by
    refine ⟨by simpa only [Set.mem_ofPred_eq, fe] using hay,?_⟩
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,fe]
    exact fun x hx => (hb _ (subset_convexHull ℝ s hx)).trans hba
  have dense : DenseRange (qCast (n:=n)) := DenseRange.piMap (fun i => Rat.denseRange_cast)
  obtain ⟨u,hu⟩ := dense.exists_mem_open ho ⟨c,hc⟩
  refine ⟨_,Or.inr ⟨u,a,rfl,?_,hu.1⟩⟩
  have ha : ∀ x ∈ s, dot (qCast u) x < (a:ℝ) := by simpa only [Set.mem_iInter,Set.mem_ofPred_eq] using hu.2
  apply convexHull_min (t := {x | dot (qCast u) x ≤ (a:ℝ)}) (fun x hx => (ha x hx).le)
  intro p hp q hq A B hA hB he
  change (∑ i, (qCast u) i * (A * p i + B * q i)) ≤ (a:ℝ)
  have calcDot : (∑ i, (qCast u) i * (A * p i + B * q i)) = A * dot (qCast u) p + B * dot (qCast u) q := by
    simp only [dot,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  rw [calcDot]
  change dot (qCast u) p ≤ (a:ℝ) at hp
  change dot (qCast u) q ≤ (a:ℝ) at hq
  nlinarith [mul_le_mul_of_nonneg_left hp hA, mul_le_mul_of_nonneg_left hq hB,
    congrArg (fun v : ℝ => v*(a:ℝ)) he]

private lemma sparse_eval {n : ℕ} {J : Type} [Fintype J] (g : J → Fin n) (v : J → ℚ)
    (x : Fin n → ℝ) :
    ∑ i, ((∑ j, if g j = i then v j else 0 : ℚ) : ℝ)*x i =
      ∑ j, (v j : ℝ)*x (g j) := by
  classical
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (g j)]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

private theorem flat_of_answers (I : Instance) (y : Fin (D I) → ℚ)
    (oracle : ∀ r : Fin I.d → Fin I.d,
      let t := y (finProdFinEquiv (Fin.last I.d, finFunctionFinEquiv r))
      0 < t → ∃ w, IsSepAnswer (Pr I r)
        (fun i => y (finProdFinEquiv (Fin.castSucc i, finFunctionFinEquiv r)) / t) w) :
    ∃ w, IsSepAnswer (KFlat I) y w := by
  classical
  let Q := KFlat I
  let Y := qCast y
  let ends (r : Fin I.d → Fin I.d) : Fin (D I) :=
    finProdFinEquiv (Fin.last I.d, finFunctionFinEquiv r)
  let coords (r : Fin I.d → Fin I.d) (i : Fin I.d) : Fin (D I) :=
    finProdFinEquiv (Fin.castSucc i, finFunctionFinEquiv r)
  by_cases hS : ∃ (v : Fin (D I) → ℚ) (a : ℚ),
      (∀ x ∈ Q, ∑ i, (v i:ℝ) * x i ≤ (a:ℝ)) ∧ (a:ℝ) < ∑ i, (v i:ℝ) * Y i
  · obtain ⟨v,a,hv,ha⟩ := hS
    exact ⟨_, Or.inr ⟨v,a,rfl,hv,ha⟩⟩
  refine ⟨[true], Or.inl ⟨rfl,?_⟩⟩
  have test {J : Type} [Fintype J] (g : J → Fin (D I)) (v : J → ℚ) (a : ℚ)
      (bound : ∀ x ∈ Q, ∑ j, (v j : ℝ)*x (g j) ≤ (a:ℝ)) :
      ∑ j, (v j : ℝ)*Y (g j) ≤ (a:ℝ) := by
    by_contra! bad
    apply hS
    exact ⟨fun i => ∑ j, if g j = i then v j else 0, a,
      fun x hx => (sparse_eval g v x).le.trans (bound x hx), (sparse_eval g v Y).symm ▸ bad⟩
  have sumEq {J : Type} [Fintype J] (g : J → Fin (D I)) (a : ℚ)
      (bound : ∀ x ∈ Q, ∑ j, x (g j) = (a:ℝ)) :
      ∑ j, Y (g j) = (a:ℝ) := by
    apply le_antisymm
    · simpa using test g (fun _ => 1) a (by intros x hx; simpa using (bound x hx).le)
    · have h := test g (fun _ => -1) (-a) (by intros x hx; simp [bound x hx])
      simpa using h
  have box (i : Fin (D I)) (a : ℕ) (bound : ∀ x ∈ Q, 0 ≤ x i ∧ x i ≤ a) :
      0 ≤ Y i ∧ Y i ≤ a := by
    have h1 := test (fun _ : Unit => i) (fun _ => -1) 0 (by intros x hx; simpa using (bound x hx).1)
    have h2 := test (fun _ : Unit => i) (fun _ => 1) a (by intros x hx; simpa using (bound x hx).2)
    exact ⟨by simpa using h1,by simpa using h2⟩
  change unflatten I Y ∈ KSet I
  refine ⟨?_,?_,?_,?_,?_⟩
  · funext i
    simp only [Finset.sum_apply]
    exact sumEq (fun r => coords r i) (I.a i) (by
      intro x hx
      simpa [unflatten,coords] using congrFun hx.1 i)
  · exact sumEq ends (I.b) (fun x hx => by exact_mod_cast hx.2.1)
  · intro r; exact box (ends r) I.b (fun x hx => hx.2.2.1 r)
  · intro r i; exact box (coords r i) (I.a i) (fun x hx => hx.2.2.2.1 r i)
  · intro r
    let z : Fin I.d → ℚ := fun i => y (coords r i)
    let t := y (ends r)
    rcases cone_separation_from_one_residue_answer I r z t (oracle r) with h | ⟨u,a,hv,hbad⟩
    · exact h
    · let g : Option (Fin I.d) → Fin (D I) := Option.elim' (ends r) (coords r)
      let v : Option (Fin I.d) → ℚ := Option.elim' a u
      have e (x : Fin (D I) → ℝ) : ∑ j, (v j:ℝ)*x (g j) =
          (∑ i, (u i:ℝ) * x (coords r i)) + (a:ℝ) * x (ends r) := by
        rw [Fintype.sum_option];simp [g,v,add_comm]
      have impossible := test g v 0 (by intro x hx; rw [e]; simpa [coords,ends,unflatten] using hv _ (hx.2.2.2.2 r))
      rw [e, Rat.cast_zero] at impossible
      have hneg : (0 : ℝ) < (∑ i, (u i:ℝ) * Y (coords r i)) + (a:ℝ) * Y (ends r) := hbad
      exact False.elim ((not_lt_of_ge impossible) hneg)

theorem solution (I : Instance) :
    (∀ (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ),
      ∃ w, IsSepAnswer (Pr I r) y w) ∧
    ∀ y : Fin (D I) → ℚ, ∃ w, IsSepAnswer (KFlat I) y w := by
  have hr (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ) :
      ∃ w, IsSepAnswer (Pr I r) y w := finite_sep _ (finite_config I r) y
  exact ⟨hr,fun y => flat_of_answers I y (fun r _ => hr r _)⟩
