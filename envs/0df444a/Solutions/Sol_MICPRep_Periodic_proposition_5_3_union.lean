-- Prove2me | solution 1 for MICPRep.Periodic.proposition_5_3_union
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:43:37.512732+00:00
-- url     : https://prove2.me/submissions/9f6eb279-4375-40e7-a012-20d1b79053b5

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

open MICPRep.Periodic

namespace MICPRep.Periodic.UnionDirect

lemma cross_bound {u v a b c d : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hub : u ^ 2 ≤ a * b) (hvd : v ^ 2 ≤ c * d) :
    2 * u * v ≤ a * d + c * b := by
  have hmul := mul_le_mul hub hvd (sq_nonneg v) (mul_nonneg ha hb)
  have hpos : 0 ≤ a * d + c * b := add_nonneg (mul_nonneg ha hd) (mul_nonneg hc hb)
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  nlinarith [sq_nonneg (a * d - c * b)]

lemma rotated_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u v : H} {a b c d l m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hu : ‖u‖ ^ 2 ≤ a * b) (hv : ‖v‖ ^ 2 ≤ c * d) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    ‖l • u + m • v‖ ^ 2 ≤ (l * a + m * c) * (l * b + m * d) := by
  have hcross := cross_bound (norm_nonneg u) (norm_nonneg v) ha hb hc hd hu hv
  have h1 := mul_le_mul_of_nonneg_left hu (sq_nonneg l)
  have h2 := mul_le_mul_of_nonneg_left hv (sq_nonneg m)
  have h3 := mul_le_mul_of_nonneg_left hcross (mul_nonneg hl hm)
  have hnorm : ‖l • u + m • v‖ ≤ l * ‖u‖ + m * ‖v‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hm]
      using norm_add_le (l • u) (m • v)
  have hnorm0 := norm_nonneg (l • u + m • v)
  have hsum0 := add_nonneg (mul_nonneg hl (norm_nonneg u)) (mul_nonneg hm (norm_nonneg v))
  nlinarith

def rotatedCone (H : Type*) [NormedAddCommGroup H] : Set (H × ℝ × ℝ) :=
  {v | 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧ ‖v.1‖ ^ 2 ≤ v.2.1 * v.2.2}

lemma rotatedCone_closed {H : Type*} [NormedAddCommGroup H] : IsClosed (rotatedCone H) := by
  exact (isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
    ((isClosed_le continuous_const (continuous_snd.comp continuous_snd)).inter
      (isClosed_le (continuous_fst.norm.pow 2)
        ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd))))

lemma rotatedCone_convex {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Convex ℝ (rotatedCone H) := by
  intro u hu v hv l m hl hm _
  refine ⟨add_nonneg (mul_nonneg hl hu.1) (mul_nonneg hm hv.1),
    add_nonneg (mul_nonneg hl hu.2.1) (mul_nonneg hm hv.2.1), ?_⟩
  exact rotated_bound hu.1 hu.2.1 hv.1 hv.2.1 hu.2.2 hv.2.2 hl hm

lemma represent_aux {n d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (C : Set (Pt n × H × (Fin d → ℝ))) (S : Set (Pt n))
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hproj : ∀ x, x ∈ S ↔ ∃ y : H, ∃ z ∈ intLattice d, (x, y, z) ∈ C)
    (hbinary : ∀ v ∈ C, v.2.2 ∈ intLattice d → ∀ i, v.2.2 i = 0 ∨ v.2.2 i = 1) :
    IsBinaryMICPR S := by
  classical
  let p := Module.finrank ℝ H
  let e : H ≃L[ℝ] (Fin p → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let L : Ambient n p d →ₗ[ℝ] (Pt n × H × (Fin d → ℝ)) :=
    { toFun := fun v => (v.1, e.symm v.2.1, v.2.2)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hL : Continuous L := by
    exact continuous_fst.prodMk ((e.symm.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))
  refine ⟨p, d, L ⁻¹' C, ⟨hclosed.preimage hL, hconvex.linear_preimage L, ?_⟩, ?_⟩
  · intro x
    rw [hproj]
    constructor
    · rintro ⟨y, z, hz, hC⟩
      refine ⟨e y, z, hz, ?_⟩
      simpa only [Set.mem_preimage, L, LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearEquiv.symm_apply_apply] using hC
    · rintro ⟨y, z, hz, hC⟩
      exact ⟨e.symm y, z, hz, hC⟩
  · intro v hv hz i
    exact hbinary (L v) hv hz i

def lattice (J : Type*) : Set (J → ℝ) :=
  Set.range (fun k : J → ℤ => fun j => (k j : ℝ))

lemma represent_finite_aux {n : ℕ} {H J : Type*} [Fintype J]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (C : Set (Pt n × H × (J → ℝ))) (S : Set (Pt n))
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hproj : ∀ x, x ∈ S ↔ ∃ y : H, ∃ z ∈ lattice J, (x, y, z) ∈ C)
    (hbinary : ∀ v ∈ C, v.2.2 ∈ lattice J → ∀ i, v.2.2 i = 0 ∨ v.2.2 i = 1) :
    IsBinaryMICPR S := by
  classical
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let L : (Pt n × H × (Fin (Fintype.card J) → ℝ)) →ₗ[ℝ] (Pt n × H × (J → ℝ)) :=
    { toFun := fun v => (v.1, v.2.1, fun j => v.2.2 (e.symm j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hL : Continuous L := by
    exact continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      (continuous_pi fun j => (continuous_apply (e.symm j)).comp (continuous_snd.comp continuous_snd)))
  apply represent_aux (L ⁻¹' C) S (hclosed.preimage hL) (hconvex.linear_preimage L)
  · intro x
    rw [hproj]
    constructor
    · rintro ⟨y, z, ⟨k, rfl⟩, hc⟩
      refine ⟨y, (fun i => (k (e i) : ℝ)), ⟨fun i => k (e i), rfl⟩, ?_⟩
      simpa [L] using hc
    · rintro ⟨y, z, ⟨k, rfl⟩, hc⟩
      exact ⟨y, (fun j => (k (e.symm j) : ℝ)), ⟨fun j => k (e.symm j), rfl⟩, hc⟩
  · rintro ⟨x, y, z⟩ hv ⟨k, rfl⟩ i
    have h := hbinary (L (x, y, fun i => (k i : ℝ))) hv
      ⟨fun j => k (e.symm j), rfl⟩ (e i)
    simpa [L] using h

abbrev UnionAux (n p₁ p₂ : ℕ) :=
  (Pt n × (Fin p₁ → ℝ)) × (Pt n × (Fin p₂ → ℝ)) × ℝ

abbrev UnionIdx (d₁ d₂ : ℕ) := Fin d₁ ⊕ (Fin d₂ ⊕ Unit)

def disjunction {n p₁ p₂ d₁ d₂ : ℕ}
    (M₁ : Set (Ambient n p₁ d₁)) (M₂ : Set (Ambient n p₂ d₂)) :
    Set (Pt n × UnionAux n p₁ p₂ × (UnionIdx d₁ d₂ → ℝ)) :=
  {v | (v.2.1.1.1, v.2.1.1.2, fun i => v.2.2 (.inl i)) ∈ M₁ ∧
    (v.2.1.2.1.1, v.2.1.2.1.2, fun i => v.2.2 (.inr (.inl i))) ∈ M₂ ∧
    (v.1 - v.2.1.1.1, v.2.1.2.2, v.2.2 (.inr (.inr ()))) ∈ rotatedCone (Pt n) ∧
    (v.1 - v.2.1.2.1.1, v.2.1.2.2, 1 - v.2.2 (.inr (.inr ()))) ∈ rotatedCone (Pt n)}

lemma disjunction_closed {n p₁ p₂ d₁ d₂ : ℕ}
    {M₁ : Set (Ambient n p₁ d₁)} {M₂ : Set (Ambient n p₂ d₂)}
    (h₁ : IsClosed M₁) (h₂ : IsClosed M₂) : IsClosed (disjunction M₁ M₂) := by
  apply IsClosed.inter
  · exact h₁.preimage (by fun_prop)
  apply IsClosed.inter
  · exact h₂.preimage (by fun_prop)
  exact (rotatedCone_closed.preimage (by fun_prop)).inter
    (rotatedCone_closed.preimage (by fun_prop))

lemma disjunction_convex {n p₁ p₂ d₁ d₂ : ℕ}
    {M₁ : Set (Ambient n p₁ d₁)} {M₂ : Set (Ambient n p₂ d₂)}
    (h₁ : Convex ℝ M₁) (h₂ : Convex ℝ M₂) : Convex ℝ (disjunction M₁ M₂) := by
  intro u hu v hv l m hl hm hlm
  refine ⟨h₁ hu.1 hv.1 hl hm hlm, h₂ hu.2.1 hv.2.1 hl hm hlm, ?_, ?_⟩
  · change (l • u.1 + m • v.1 - (l • u.2.1.1.1 + m • v.2.1.1.1),
      l * u.2.1.2.2 + m * v.2.1.2.2,
      l * u.2.2 (.inr (.inr ())) + m * v.2.2 (.inr (.inr ()))) ∈ rotatedCone (Pt n)
    have heq : l • u.1 + m • v.1 - (l • u.2.1.1.1 + m • v.2.1.1.1) =
        l • (u.1 - u.2.1.1.1) + m • (v.1 - v.2.1.1.1) := by module
    rw [heq]
    exact rotatedCone_convex hu.2.2.1 hv.2.2.1 hl hm hlm
  · change (l • u.1 + m • v.1 - (l • u.2.1.2.1.1 + m • v.2.1.2.1.1),
      l * u.2.1.2.2 + m * v.2.1.2.2,
      1 - (l * u.2.2 (.inr (.inr ())) + m * v.2.2 (.inr (.inr ())))) ∈ rotatedCone (Pt n)
    have heq : l • u.1 + m • v.1 - (l • u.2.1.2.1.1 + m • v.2.1.2.1.1) =
        l • (u.1 - u.2.1.2.1.1) + m • (v.1 - v.2.1.2.1.1) := by module
    have hlast : 1 - (l * u.2.2 (.inr (.inr ())) + m * v.2.2 (.inr (.inr ()))) =
        l * (1 - u.2.2 (.inr (.inr ()))) + m * (1 - v.2.2 (.inr (.inr ()))) := by nlinarith
    rw [heq, hlast]
    exact rotatedCone_convex hu.2.2.2 hv.2.2.2 hl hm hlm

lemma lattice_comp {J K : Type*} {z : J → ℝ} (hz : z ∈ lattice J) (f : K → J) :
    (fun i => z (f i)) ∈ lattice K := by
  obtain ⟨k, rfl⟩ := hz
  exact ⟨fun i => k (f i), rfl⟩

def mergeZ {d₁ d₂ : ℕ} (z₁ : Fin d₁ → ℝ) (z₂ : Fin d₂ → ℝ) (r : ℝ) :
    UnionIdx d₁ d₂ → ℝ := Sum.elim z₁ (Sum.elim z₂ (fun _ => r))

lemma mergeZ_lattice {d₁ d₂ : ℕ} {z₁ : Fin d₁ → ℝ} {z₂ : Fin d₂ → ℝ}
    (h₁ : z₁ ∈ intLattice d₁) (h₂ : z₂ ∈ intLattice d₂) (r : ℤ) :
    mergeZ z₁ z₂ (r : ℝ) ∈ lattice (UnionIdx d₁ d₂) := by
  obtain ⟨k₁, rfl⟩ := h₁
  obtain ⟨k₂, rfl⟩ := h₂
  refine ⟨Sum.elim k₁ (Sum.elim k₂ (fun _ => r)), ?_⟩
  ext (i | (i | i)) <;> rfl

lemma selector_binary {n p₁ p₂ d₁ d₂ : ℕ}
    {M₁ : Set (Ambient n p₁ d₁)} {M₂ : Set (Ambient n p₂ d₂)}
    {v : Pt n × UnionAux n p₁ p₂ × (UnionIdx d₁ d₂ → ℝ)}
    (hv : v ∈ disjunction M₁ M₂) (hz : v.2.2 ∈ lattice (UnionIdx d₁ d₂)) :
    v.2.2 (.inr (.inr ())) = 0 ∨ v.2.2 (.inr (.inr ())) = 1 := by
  obtain ⟨k, hk⟩ := hz
  have h0 : 0 ≤ (k (.inr (.inr ())) : ℝ) := by
    simpa only [← hk] using hv.2.2.1.2.1
  have h1 : (k (.inr (.inr ())) : ℝ) ≤ 1 := by
    have h := hv.2.2.2.2.1
    rw [← hk] at h
    change 0 ≤ 1 - (k (.inr (.inr ())) : ℝ) at h
    linarith
  have hk0 : 0 ≤ k (.inr (.inr ())) := by exact_mod_cast h0
  have hk1 : k (.inr (.inr ())) ≤ 1 := by exact_mod_cast h1
  have h : k (.inr (.inr ())) = 0 ∨ k (.inr (.inr ())) = 1 := by omega
  rw [← hk]
  rcases h with h | h <;> simp [h]

lemma disjunction_rep {n p₁ p₂ d₁ d₂ : ℕ}
    {M₁ : Set (Ambient n p₁ d₁)} {M₂ : Set (Ambient n p₂ d₂)}
    {S T : Set (Pt n)} (h₁ : Induces M₁ S) (h₂ : Induces M₂ T)
    (hne₁ : S.Nonempty) (hne₂ : T.Nonempty) :
    ∀ x, x ∈ S ∪ T ↔ ∃ y : UnionAux n p₁ p₂,
      ∃ z ∈ lattice (UnionIdx d₁ d₂), (x, y, z) ∈ disjunction M₁ M₂ := by
  intro x
  constructor
  · rintro (hx | hx)
    · obtain ⟨y₁, z₁, hz₁, hm₁⟩ := (h₁.2.2 x).mp hx
      obtain ⟨x₂, hx₂⟩ := hne₂
      obtain ⟨y₂, z₂, hz₂, hm₂⟩ := (h₂.2.2 x₂).mp hx₂
      refine ⟨((x, y₁), (x₂, y₂), ‖x - x₂‖ ^ 2), mergeZ z₁ z₂ 0,
        by simpa only [Int.cast_zero] using mergeZ_lattice hz₁ hz₂ 0, hm₁, hm₂, ?_, ?_⟩
      · exact ⟨sq_nonneg _, le_rfl, by simp [mergeZ]⟩
      · exact ⟨sq_nonneg _, by norm_num [mergeZ], by simp [mergeZ]⟩
    · obtain ⟨y₂, z₂, hz₂, hm₂⟩ := (h₂.2.2 x).mp hx
      obtain ⟨x₁, hx₁⟩ := hne₁
      obtain ⟨y₁, z₁, hz₁, hm₁⟩ := (h₁.2.2 x₁).mp hx₁
      refine ⟨((x₁, y₁), (x, y₂), ‖x - x₁‖ ^ 2), mergeZ z₁ z₂ 1,
        by simpa only [Int.cast_one] using mergeZ_lattice hz₁ hz₂ 1, hm₁, hm₂, ?_, ?_⟩
      · exact ⟨sq_nonneg _, by norm_num [mergeZ], by simp [mergeZ]⟩
      · exact ⟨sq_nonneg _, by norm_num [mergeZ], by simp [mergeZ]⟩
  · rintro ⟨y, z, hz, hv⟩
    rcases selector_binary hv hz with hzero | hone
    · change z (.inr (.inr ())) = 0 at hzero
      have hnorm := hv.2.2.1.2.2
      change ‖x - y.1.1‖ ^ 2 ≤ y.2.2 * z (.inr (.inr ())) at hnorm
      rw [hzero, mul_zero] at hnorm
      have hx : x = y.1.1 := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y.1.1)]))
      left
      rw [hx]
      exact (h₁.2.2 _).mpr ⟨y.1.2, (fun i => z (.inl i)), lattice_comp hz Sum.inl, hv.1⟩
    · change z (.inr (.inr ())) = 1 at hone
      have hnorm := hv.2.2.2.2.2
      change ‖x - y.2.1.1‖ ^ 2 ≤ y.2.2 * (1 - z (.inr (.inr ()))) at hnorm
      rw [hone, sub_self, mul_zero] at hnorm
      have hx : x = y.2.1.1 := sub_eq_zero.mp
        (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y.2.1.1)]))
      right
      rw [hx]
      exact (h₂.2.2 _).mpr ⟨y.2.1.2, (fun i => z (.inr (.inl i))),
        lattice_comp hz (fun i => Sum.inr (Sum.inl i)), hv.2.1⟩

lemma binary_union {n : ℕ} {S T : Set (Pt n)}
    (hS : IsBinaryMICPR S) (hT : IsBinaryMICPR T) : IsBinaryMICPR (S ∪ T) := by
  classical
  by_cases hne₁ : S.Nonempty
  swap
  · simpa only [Set.not_nonempty_iff_eq_empty.mp hne₁, Set.empty_union] using hT
  by_cases hne₂ : T.Nonempty
  swap
  · simpa only [Set.not_nonempty_iff_eq_empty.mp hne₂, Set.union_empty] using hS
  obtain ⟨p₁, d₁, M₁, hM₁, hb₁⟩ := hS
  obtain ⟨p₂, d₂, M₂, hM₂, hb₂⟩ := hT
  apply represent_finite_aux (disjunction M₁ M₂) (S ∪ T)
    (disjunction_closed hM₁.1 hM₂.1) (disjunction_convex hM₁.2.1 hM₂.2.1)
    (disjunction_rep hM₁ hM₂ hne₁ hne₂)
  intro v hv hz i
  rcases i with i | (i | i)
  · exact hb₁ _ hv.1 (lattice_comp hz Sum.inl) i
  · exact hb₂ _ hv.2.1 (lattice_comp hz (fun j => Sum.inr (Sum.inl j))) i
  · cases i
    exact selector_binary hv hz

lemma binary_empty (n : ℕ) : IsBinaryMICPR (∅ : Set (Pt n)) := by
  refine ⟨0, 0, ∅, ⟨isClosed_empty, convex_empty, ?_⟩, ?_⟩
  · intro x
    simp
  · intro q hq
    exact False.elim hq

lemma finite_union {n k : ℕ} (S : Fin k → Set (Pt n))
    (hS : ∀ i, IsBinaryMICPR (S i)) : IsBinaryMICPR (⋃ i, S i) := by
  induction k with
  | zero => simpa using binary_empty n
  | succ k ih =>
    have hset : (⋃ i : Fin (k + 1), S i) = S 0 ∪ ⋃ i : Fin k, S i.succ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ (fun j => ?_) i hi
        · exact Or.inl
        · intro hj
          exact Or.inr ⟨j, hj⟩
      · rintro (h | ⟨j, h⟩)
        · exact ⟨0, h⟩
        · exact ⟨j.succ, h⟩
    rw [hset]
    exact binary_union (hS 0) (ih (fun i => S i.succ) (fun i => hS i.succ))

end MICPRep.Periodic.UnionDirect

/-- Proposition 5.3, p. 17 (finite-union clause for binary MICP-R sets). -/
theorem solution {n k : ℕ} (S : Fin k → Set (Pt n))
    (hS : ∀ i, IsBinaryMICPR (S i)) :
    IsBinaryMICPR (⋃ i, S i) := by
  exact MICPRep.Periodic.UnionDirect.finite_union S hS
