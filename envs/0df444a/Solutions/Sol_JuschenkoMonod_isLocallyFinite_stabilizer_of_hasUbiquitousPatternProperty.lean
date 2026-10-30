-- Prove2me | solution 1 for JuschenkoMonod.isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:54:31.701094+00:00
-- url     : https://prove2.me/submissions/551112b4-f9b9-493d-b804-bf906b54019f

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_Chou_Classes
import Definitions.Def_JuschenkoMonod

open scoped Pointwise

namespace JuschenkoMonod


section LemmaA

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

lemma finite_homs_of_closure (S : Set Γ) (hS : S.Finite) (n : ℕ) :
    Finite (Subgroup.closure S →* Equiv.Perm (Fin n)) := by
  set S' : Set (Subgroup.closure S) := ((↑) : Subgroup.closure S → Γ) ⁻¹' S with hS'
  have hfin : S'.Finite := hS.preimage Subtype.val_injective.injOn
  have : Finite S' := hfin.to_subtype
  refine Finite.of_injective (fun f : Subgroup.closure S →* Equiv.Perm (Fin n) =>
    fun s : S' => f s.1) ?_
  intro f g hfg
  apply MonoidHom.eq_of_eqOn_top
  rw [← Subgroup.closure_closure_coe_preimage (k := S)]
  apply MonoidHom.eqOn_closure
  intro s hs
  exact congrFun hfg ⟨s, hs⟩

lemma finite_closure_of_bounded_orbits [FaithfulSMul Γ X] (S : Set Γ) (hS : S.Finite) (N : ℕ)
    (horb : ∀ x : X, (MulAction.orbit (Subgroup.closure S) x).Finite ∧
      (MulAction.orbit (Subgroup.closure S) x).ncard ≤ N) :
    Finite (Subgroup.closure S) := by
  set H := Subgroup.closure S with hH
  have hO : ∀ x : X, Finite (MulAction.orbit H x) := fun x => (horb x).1.to_subtype
  let n : X → ℕ := fun x => Nat.card (MulAction.orbit H x)
  have hn : ∀ x, n x ≤ N := fun x => by
    have := (horb x).2
    show Nat.card (MulAction.orbit H x) ≤ N
    rw [Nat.card_coe_set_eq]; exact this
  let e : ∀ x, MulAction.orbit H x ≃ Fin (n x) := fun x => @Finite.equivFin _ (hO x)
  let f : ∀ x, H →* Equiv.Perm (Fin (n x)) := fun x =>
    ((e x).permCongrHom : Equiv.Perm (MulAction.orbit H x) →* Equiv.Perm (Fin (n x))).comp
      (MulAction.toPermHom H (MulAction.orbit H x))
  let K : X → Subgroup H := fun x => (f x).ker
  have hKfin : ∀ x, (K x).FiniteIndex := fun x => by
    refine ⟨?_⟩
    show (f x).ker.index ≠ 0
    rw [Subgroup.index_ker]
    have : Finite (f x).range := inferInstance
    exact Nat.card_pos.ne'
  have hrange : (Set.range K).Finite := by
    have : Set.range K ⊆ ⋃ m ∈ Finset.range (N + 1),
        Set.range (fun f : H →* Equiv.Perm (Fin m) => f.ker) := by
      rintro _ ⟨x, rfl⟩
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_range]
      exact ⟨n x, Nat.lt_succ_of_le (hn x), f x, rfl⟩
    refine Set.Finite.subset ?_ this
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun m _ => ?_
    have := finite_homs_of_closure S hS m
    exact Set.finite_range _
  have : Finite (Set.range K) := hrange.to_subtype
  have hinf : (⨅ x, K x) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_iInf] at hh
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    have h1 := hh x
    simp only [K, MonoidHom.mem_ker, f, MonoidHom.comp_apply] at h1
    have h2 : MulAction.toPermHom H (MulAction.orbit H x) h = 1 := by
      exact (map_eq_one_iff _ (e x).permCongrHom.injective).mp h1
    have h3 := congrArg (fun p : Equiv.Perm (MulAction.orbit H x) =>
      (p ⟨x, MulAction.mem_orbit_self x⟩ : X)) h2
    have h4 : h • x = x := by simpa using h3
    show (h : Γ) • x = (1 : Γ) • x
    rw [one_smul]; exact h4
  have hfi : (⨅ x, K x).FiniteIndex := by
    rw [← iInf_range' (fun k : Subgroup H => k) K] 
    exact Subgroup.finiteIndex_iInf (f := fun k : Set.range K => k.1)
      (fun k => by obtain ⟨x, hx⟩ := k.2; rw [← hx]; exact hKfin x)
  rw [hinf] at hfi
  have := hfi.index_ne_zero
  rw [Subgroup.index_bot] at this
  exact Nat.finite_of_card_ne_zero this

end LemmaA

end JuschenkoMonod

namespace JuschenkoMonod

section LemmaC

/-- The block `B_i` of the proof of Lemma 4.1, for consecutive windows centred at `T < T'`. -/
def inBlock (A : Set ℤ) (n : ℤ) (T T' x : ℤ) : Prop :=
  (-n ≤ x - T ∧ x - T ≤ n ∧ x - T ∈ A) ∨
    (T + n < x ∧ x ≤ T' + n ∧ ¬ (-n ≤ x - T' ∧ x - T' ≤ n ∧ x - T' ∈ A))

lemma inBlock_map (A : Set ℤ) (c m : ℤ) (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hA1 : ∀ y, c < y → y ∈ A) (hA2 : ∀ y, y < -c → y ∉ A)
    (g : Equiv.Perm ℤ) (hgA : ∀ y, y ∈ A ↔ g y ∈ A) (hgm : ∀ y, |g y - y| ≤ m)
    (T T' : ℤ) (hTT : T + 2 * (c + 2 * m) + 1 ≤ T')
    (hgT : ∀ e, -(c + 2 * m) ≤ e → e ≤ c + 2 * m → g (e + T) = g e + T)
    (hgT' : ∀ e, -(c + 2 * m) ≤ e → e ≤ c + 2 * m → g (e + T') = g e + T')
    (x : ℤ) (hx : inBlock A (c + 2 * m) T T' x) : inBlock A (c + 2 * m) T T' (g x) := by
  have hgm' : ∀ y, g y - y ≤ m ∧ y - g y ≤ m := fun y => by
    have := abs_le.mp (hgm y); constructor <;> linarith [this.1, this.2]
  unfold inBlock at hx ⊢
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- x lies in the A-part of the window at T
    set e := x - T with he
    have hxe : x = e + T := by omega
    have hg := hgT e h1 h2
    rw [hxe, hg]
    have hAe := (hgA e).mp h3
    have hb := hgm' e
    have hge : -c ≤ g e := by
      by_contra hlt; exact hA2 _ (by omega) hAe
    by_cases hle : g e ≤ c + 2 * m
    · left; refine ⟨by omega, by omega, ?_⟩
      simpa using hAe
    · right
      refine ⟨by omega, by omega, ?_⟩
      intro ⟨a, b, d⟩
      exact hA2 _ (by omega) d
  · -- x lies in the right part
    by_cases hw : -(c + 2 * m) ≤ x - T' ∧ x - T' ≤ c + 2 * m
    · -- window at T', outside A
      set e := x - T' with he
      have hxe : x = e + T' := by omega
      have hnA : e ∉ A := fun hA => h3 ⟨hw.1, hw.2, hA⟩
      have hg := hgT' e hw.1 hw.2
      rw [hxe, hg]
      have hnAg : g e ∉ A := fun hh => hnA ((hgA e).mpr hh)
      have hb := hgm' e
      have hle : g e ≤ c := by
        by_contra hlt; exact hnAg (hA1 _ (by omega))
      by_cases hgt : T + (c + 2 * m) < g e + T'
      · right
        refine ⟨hgt, by omega, ?_⟩
        intro ⟨a, b, d⟩
        simp only [add_sub_cancel_right] at d
        exact hnAg d
      · left
        refine ⟨by omega, by omega, ?_⟩
        apply hA1; omega
    · -- below the window at T'
      have hlt : x - T' < -(c + 2 * m) := by omega
      have hb := hgm' x
      by_cases hgt : T + (c + 2 * m) < g x
      · right
        refine ⟨hgt, by omega, ?_⟩
        intro ⟨a, b, d⟩
        exact hA2 _ (by omega) d
      · left
        refine ⟨by omega, by omega, ?_⟩
        apply hA1; omega

lemma exists_invariant_block (A : Set ℤ) (c m k : ℤ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hk0 : 0 ≤ k)
    (hA1 : ∀ y, c < y → y ∈ A) (hA2 : ∀ y, y < -c → y ∉ A)
    (F : Set (Equiv.Perm ℤ)) (hFA : ∀ g ∈ F, ∀ y, y ∈ A ↔ g y ∈ A)
    (hFm : ∀ g ∈ F, ∀ y, |g y - y| ≤ m)
    (hk : ∀ j : ℤ, ∃ t : ℤ, Set.Icc (t - (c + 2 * m)) (t + (c + 2 * m)) ⊆ Set.Icc (j - k) (j + k) ∧
      ∀ i, -(c + 2 * m) ≤ i → i ≤ c + 2 * m → ∀ g ∈ F, g (i + t) = g i + t) (x : ℤ) :
    ∃ a : ℤ, ∃ B : Set ℤ, x ∈ B ∧ B ⊆ Set.Icc a (a + 4 * k + 1) ∧ ∀ g ∈ F, ∀ y ∈ B, g y ∈ B := by
  choose t ht using fun i : ℤ => hk (i * (2 * k + 1))
  have hlo : ∀ i, i * (2 * k + 1) - k ≤ t i - (c + 2 * m) := fun i =>
    ((ht i).1 (Set.left_mem_Icc.mpr (by omega))).1
  have hhi : ∀ i, t i + (c + 2 * m) ≤ i * (2 * k + 1) + k := fun i =>
    ((ht i).1 (Set.right_mem_Icc.mpr (by omega))).2
  have hstep : ∀ i : ℤ, (i + 1) * (2 * k + 1) = i * (2 * k + 1) + (2 * k + 1) := fun i => by ring
  have hsep : ∀ i, t i + 2 * (c + 2 * m) + 1 ≤ t (i + 1) := fun i => by
    have h1 := hlo (i + 1); have h2 := hhi i; rw [hstep i] at h1; omega
  have hcover : ∀ x, ∃ i, inBlock A (c + 2 * m) (t i) (t (i + 1)) x := by
    intro x
    have hd : 0 < 2 * k + 1 := by omega
    obtain ⟨q, hq⟩ : ∃ q : ℤ, q * (2 * k + 1) - k ≤ x ∧ x ≤ q * (2 * k + 1) + k := by
      refine ⟨(x + k) / (2 * k + 1), ?_, ?_⟩
      · have := Int.ediv_mul_le (x + k) hd.ne'
        omega
      · have := Int.lt_ediv_add_one_mul_self (x + k) hd
        rw [add_mul, one_mul] at this
        omega
    obtain ⟨i0, h1, h2⟩ : ∃ i0, t i0 + (c + 2 * m) < x ∧ x ≤ t (i0 + 1) + (c + 2 * m) := by
      by_cases hxq : x ≤ t q + (c + 2 * m)
      · refine ⟨q - 1, ?_, by simpa using hxq⟩
        have := hhi (q - 1)
        have h3 : (q - 1) * (2 * k + 1) = q * (2 * k + 1) - (2 * k + 1) := by ring
        omega
      · refine ⟨q, by omega, ?_⟩
        have := hlo (q + 1)
        rw [hstep q] at this
        omega
    by_cases hE : -(c + 2 * m) ≤ x - t (i0 + 1) ∧ x - t (i0 + 1) ≤ c + 2 * m ∧ x - t (i0 + 1) ∈ A
    · exact ⟨i0 + 1, Or.inl hE⟩
    · exact ⟨i0, Or.inr ⟨h1, h2, hE⟩⟩
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨i * (2 * k + 1) - k, {y | inBlock A (c + 2 * m) (t i) (t (i + 1)) y}, hi, ?_, ?_⟩
  · intro y hy
    have h1 := hlo i; have h2 := hhi i; have h3 := hhi (i + 1); rw [hstep i] at h3
    simp only [Set.mem_setOf_eq, inBlock] at hy
    rcases hy with ⟨a, b, _⟩ | ⟨a, b, _⟩ <;> simp only [Set.mem_Icc] <;> omega
  · intro g hg y hy
    exact inBlock_map A c m hc hm hA1 hA2 g (hFA g hg) (hFm g hg) (t i) (t (i + 1)) (hsep i)
      (fun e h1 h2 => (ht i).2 e h1 h2 g hg) (fun e h1 h2 => (ht (i + 1)).2 e h1 h2 g hg) y hy

end LemmaC

end JuschenkoMonod

namespace JuschenkoMonod

theorem lemma41_gen (G : Subgroup (Equiv.Perm ℤ))
    (hG : G ≤ IntervalExchange.wobbling ℤ) (hU : HasUbiquitousPatternProperty G)
    (A : Set ℤ) (c : ℕ) (hA1 : ∀ y : ℤ, (c : ℤ) < y → y ∈ A) (hA2 : ∀ y : ℤ, y < -(c : ℤ) → y ∉ A) :
    Chou.IsLocallyFinite (MulAction.stabilizer G A) := by
  classical
  intro S hS
  set S' : Set (MulAction.stabilizer G A) := S ∪ (fun s => s⁻¹) '' S with hS'
  have hS'fin : S'.Finite := hS.union (hS.image _)
  set F : Finset G := hS'fin.toFinset.image (fun γ => (γ.1 : G)) with hF
  have hFmem : ∀ g ∈ F, ∃ γ ∈ S', γ.1 = g := fun g hg => by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨γ, hS'fin.mem_toFinset.mp hγ, rfl⟩
  have hstab : ∀ γ : MulAction.stabilizer G A, ∀ y : ℤ, y ∈ A ↔ (γ.1.1 : Equiv.Perm ℤ) y ∈ A := by
    intro γ y
    have h : γ.1 • A = A := γ.2
    have := Set.smul_mem_smul_set_iff (a := γ.1) (x := y) (s := A)
    rw [h] at this
    exact this.symm
  -- displacement bound
  have hbd : ∃ m : ℕ, ∀ g ∈ F, ∀ y : ℤ, |(g.1 : Equiv.Perm ℤ) y - y| ≤ m := by
    have h1 : ∀ g : G, ∃ C : ℝ, ∀ y : ℤ, |((g.1 y - y : ℤ) : ℝ)| ≤ C := fun g => by
      obtain ⟨C, hC⟩ := hG g.2
      exact ⟨C, fun y => by simpa [Int.dist_eq, abs_sub_comm] using hC y⟩
    choose C hC using h1
    refine ⟨⌈∑ g ∈ F, |C g|⌉₊, fun g hg y => ?_⟩
    have h2 : |((g.1 y - y : ℤ) : ℝ)| ≤ ∑ g ∈ F, |C g| :=
      (hC g y).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun g => |C g|) (fun _ _ => abs_nonneg _) hg))
    have h3 := h2.trans (Nat.le_ceil _)
    exact_mod_cast h3
  obtain ⟨m, hm⟩ := hbd
  obtain ⟨k, hk⟩ := hU F (c + 2 * m)
  set Fp : Set (Equiv.Perm ℤ) := {σ | ∃ g ∈ F, g.1 = σ} with hFp
  have hblock : ∀ x : ℤ, ∃ a : ℤ, ∃ B : Set ℤ, x ∈ B ∧ B ⊆ Set.Icc a (a + 4 * (k : ℤ) + 1) ∧
      ∀ σ ∈ Fp, ∀ y ∈ B, σ y ∈ B := by
    intro x
    refine exists_invariant_block A c m k (by positivity) (by positivity) (by positivity) hA1 hA2 Fp
      ?_ ?_ ?_ x
    · rintro σ ⟨g, hg, rfl⟩ y
      obtain ⟨γ, _, rfl⟩ := hFmem g hg
      exact hstab γ y
    · rintro σ ⟨g, hg, rfl⟩ y
      exact hm g hg y
    · intro j
      obtain ⟨t, h1, h2⟩ := hk j
      refine ⟨t, ?_, ?_⟩
      · simpa using h1
      · rintro i hi1 hi2 σ ⟨g, hg, rfl⟩
        exact h2 i (Set.mem_Icc.mpr ⟨by push_cast; exact hi1, by push_cast; exact hi2⟩) g hg
  refine finite_closure_of_bounded_orbits (X := ℤ) S hS (4 * k + 2) fun x => ?_
  obtain ⟨a, B, hxB, hBsub, hBinv⟩ := hblock x
  have hgen : ∀ s ∈ S, ∀ y ∈ B, s • y ∈ B ∧ s⁻¹ • y ∈ B := by
    intro s hs y hy
    constructor
    · exact hBinv _ ⟨s.1, Finset.mem_image.mpr ⟨s, hS'fin.mem_toFinset.mpr (Or.inl hs), rfl⟩, rfl⟩ y hy
    · exact hBinv _ ⟨(s⁻¹).1, Finset.mem_image.mpr
        ⟨s⁻¹, hS'fin.mem_toFinset.mpr (Or.inr ⟨s, hs, rfl⟩), rfl⟩, rfl⟩ y hy
  have hall : ∀ h ∈ Subgroup.closure S, (∀ y ∈ B, h • y ∈ B) ∧ (∀ y ∈ B, h⁻¹ • y ∈ B) := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem s hs => exact ⟨fun y hy => (hgen s hs y hy).1, fun y hy => (hgen s hs y hy).2⟩
    | one => exact ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
    | mul a b _ _ ha hb =>
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [mul_smul]; exact ha.1 _ (hb.1 y hy)
      · rw [mul_inv_rev, mul_smul]; exact hb.2 _ (ha.2 y hy)
    | inv a _ ha => exact ⟨ha.2, fun y hy => by simpa using ha.1 y hy⟩
  have horb : MulAction.orbit (Subgroup.closure S) x ⊆ B := by
    rintro _ ⟨h, rfl⟩
    exact (hall h.1 h.2).1 x hxB
  have hsub : MulAction.orbit (Subgroup.closure S) x ⊆ Set.Icc a (a + 4 * (k : ℤ) + 1) :=
    horb.trans hBsub
  refine ⟨(Set.finite_Icc _ _).subset hsub, ?_⟩
  calc (MulAction.orbit (Subgroup.closure S) x).ncard
      ≤ (Set.Icc a (a + 4 * (k : ℤ) + 1)).ncard := Set.ncard_le_ncard hsub (Set.finite_Icc _ _)
    _ = 4 * k + 2 := by
      rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]; omega

theorem lemma41_aux (G : Subgroup (Equiv.Perm ℤ))
    (hG : G ≤ IntervalExchange.wobbling ℤ) (hU : HasUbiquitousPatternProperty G) (E : Finset ℤ) :
    Chou.IsLocallyFinite (MulAction.stabilizer G (symmDiff (E : Set ℤ) natSet)) := by
  classical
  have hEc : ∀ e ∈ E, (e.natAbs : ℤ) ≤ ((∑ e ∈ E, e.natAbs : ℕ) : ℤ) := fun e he => by
    have : e.natAbs ≤ ∑ e ∈ E, e.natAbs :=
      Finset.single_le_sum (f := fun e : ℤ => e.natAbs) (fun _ _ => Nat.zero_le _) he
    exact_mod_cast this
  refine lemma41_gen G hG hU _ (∑ e ∈ E, e.natAbs) ?_ ?_
  · intro y hy
    have h1 : y ∉ (E : Set ℤ) := fun h => by have := hEc y h; omega
    have h2 : y ∈ natSet := ⟨y.toNat, by simp; omega⟩
    exact Or.inr ⟨h2, h1⟩
  · intro y hy hyA
    have h1 : y ∉ (E : Set ℤ) := fun h => by have := hEc y h; omega
    have h2 : y ∉ natSet := fun ⟨n, hn⟩ => by omega
    rcases hyA with ⟨a, _⟩ | ⟨a, _⟩
    · exact h1 a
    · exact h2 a

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.lemma41_aux := @JuschenkoMonod.lemma41_aux
