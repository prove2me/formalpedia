-- Prove2me | solution 1 for JMMS.exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:22:18.266823+00:00
-- url     : https://prove2.me/submissions/fba4400f-7505-439c-8e3f-f1ae9486a1dc

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isAmenable_iff_isExtensivelyAmenable_of_le_IET
import Theorems.Thm_JMMS_isExtensivelyAmenable_tfae

section

open IntervalExchange

namespace JMMS

namespace IETQ

/-- A finitely generated abelian group embeds injectively in some `ℤ^d` with bounded jumps
along each fixed translation (via `A ≅ ℤⁿ × T`, `T` finite). -/
lemma exists_embedding {A : Type*} [AddCommGroup A] [AddGroup.FG A] :
    ∃ (d : ℕ) (ψ : A → Fin d → ℤ), Function.Injective ψ ∧
      ∀ s : A, ∃ L : ℕ, ∀ a : A, ∀ i, |ψ (a + s) i - ψ a i| ≤ L := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  set T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : Finite T := Finite.of_injective (fun x : T => (fun i => x i)) DFunLike.coe_injective
  let N : ℕ := Nat.card T
  let ιT : T → ℤ := fun t => ((Finite.equivFin T t : Fin N) : ℕ)
  have hι0 : ∀ t, 0 ≤ ιT t := fun t => Int.natCast_nonneg _
  have hι1 : ∀ t, ιT t < N := fun t => by
    simp only [ιT]; exact_mod_cast (Finite.equivFin T t).isLt
  have hιinj : Function.Injective ιT := by
    intro a b h
    simp only [ιT, Nat.cast_inj] at h
    exact (Finite.equivFin T).injective (Fin.ext h)
  let ψ : A → Fin (n + 1) → ℤ := fun a => Fin.cons (ιT (f a).2) (fun j => (f a).1 j)
  refine ⟨n + 1, ψ, ?_, fun s => ?_⟩
  · intro a b h
    have h0 := congrFun h 0
    simp only [ψ, Fin.cons_zero] at h0
    apply f.injective
    refine Prod.ext ?_ (hιinj h0)
    ext j
    have := congrFun h j.succ
    simpa [ψ] using this
  · refine ⟨N + ∑ j, ((f s).1 j).natAbs, fun a i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ψ, Fin.cons_zero, map_add, Prod.snd_add]
      have := hι0 ((f a).2 + (f s).2); have := hι1 ((f a).2 + (f s).2)
      have := hι0 (f a).2; have := hι1 (f a).2
      have : |ιT ((f a).2 + (f s).2) - ιT (f a).2| ≤ N := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 : (0 : ℤ) ≤ ((∑ j, ((f s).1 j).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      push_cast at h2 ⊢
      linarith
    · simp only [ψ, Fin.cons_succ, map_add, Prod.fst_add, Finsupp.coe_add, Pi.add_apply,
        add_sub_cancel_left]
      have h1 : ((f s).1 j).natAbs ≤ ∑ j, ((f s).1 j).natAbs :=
        Finset.single_le_sum (f := fun j => ((f s).1 j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      rw [Int.abs_eq_natAbs]
      push_cast
      have : (((f s).1 j).natAbs : ℤ) ≤ ((∑ j, ((f s).1 j).natAbs : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this
      linarith [Int.natCast_nonneg N]

/-- Every element of `IET` has finitely many angles. -/
theorem angles_finite_of_mem_IET {g : Equiv.Perm UnitAddCircle} (hg : g ∈ IET) :
    (angles g).Finite := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2.1
  | one => exact (Set.finite_singleton 0).subset (by rintro _ ⟨x, rfl⟩; simp)
  | mul g h _ _ hg hh =>
    refine (hg.add hh).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨g (h x) - h x, ⟨h x, rfl⟩, h x - x, ⟨x, rfl⟩, ?_⟩
    simp [Equiv.Perm.mul_apply]
  | inv g _ hg =>
    refine hg.neg.subset ?_
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_neg]
    exact ⟨g⁻¹ x, by simp⟩

/-- Part (a), integer form: an injective map of each orbit into `ℤ^d` whose coordinates move by
at most `L` along each generator. -/
theorem exists_embedding_orbit (G : Subgroup (Equiv.Perm UnitAddCircle)) (hG : G ≤ IET)
    (S : Finset (Equiv.Perm UnitAddCircle)) (hS : ∀ s ∈ S, s ∈ G)
    (hcl : Subgroup.closure (S : Set (Equiv.Perm UnitAddCircle)) = G) (x : UnitAddCircle) :
    ∃ (d : ℕ) (f : UnitAddCircle → (Fin d → ℤ)) (L : ℕ),
      Set.InjOn f (MulAction.orbit G x) ∧
        ∀ y ∈ MulAction.orbit G x, ∀ s ∈ S, ∀ i, |f (s y) i - f y i| ≤ L := by
  classical
  set Λ : AddSubgroup UnitAddCircle := AddSubgroup.closure (⋃ s ∈ S, angles s) with hΛ
  have hang : ∀ s ∈ S, ∀ z, s z - z ∈ Λ := fun s hs z =>
    AddSubgroup.subset_closure (Set.mem_biUnion hs ⟨z, rfl⟩)
  have hΛfg : Λ.FG := by
    refine ⟨(S.finite_toSet.biUnion fun g hg => angles_finite_of_mem_IET (hG (hS g hg))).toFinset,
      ?_⟩
    simp [hΛ]
  have : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).mpr hΛfg
  obtain ⟨d, ψ, hψ, hjump⟩ := exists_embedding (A := Λ)
  -- every element of `G` moves points by elements of `Λ`
  have hGΛ : ∀ g ∈ G, ∀ z, g z - z ∈ Λ := by
    intro g hg
    rw [← hcl] at hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hang s hs
    | one => intro z; simp
    | mul g h _ _ hg hh =>
      intro z
      have := Λ.add_mem (hg (h z)) (hh z)
      simpa [Equiv.Perm.mul_apply] using this
    | inv g _ hg =>
      intro z
      have := Λ.neg_mem (hg (g⁻¹ z))
      simpa using this
  have horb : ∀ y ∈ MulAction.orbit G x, y - x ∈ Λ := by
    rintro y ⟨g, rfl⟩
    exact hGΛ g g.2 x
  let f : UnitAddCircle → Fin d → ℤ := fun y => if h : y - x ∈ Λ then ψ ⟨y - x, h⟩ else 0
  have hf : ∀ y (h : y - x ∈ Λ), f y = ψ ⟨y - x, h⟩ := fun y h => dif_pos h
  -- the jumps
  let J : Set Λ := {a | ∃ s ∈ S, (a : UnitAddCircle) ∈ angles s}
  have hJfin : J.Finite := by
    have h1 : (⋃ s ∈ (S : Set (Equiv.Perm UnitAddCircle)), angles s).Finite :=
      S.finite_toSet.biUnion fun g hg => angles_finite_of_mem_IET (hG (hS g hg))
    refine (h1.preimage Subtype.val_injective.injOn).subset ?_
    rintro a ⟨s, hs, ha⟩
    exact Set.mem_biUnion (x := s) hs ha
  choose Lf hLf using hjump
  obtain ⟨L, hL⟩ := (hJfin.image Lf).bddAbove
  refine ⟨d, f, L, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hf a (horb a ha), hf b (horb b hb)] at hab
    have := congrArg Subtype.val (hψ hab)
    simpa using this
  · intro y hy s hs i
    have hy' := horb y hy
    have hsy : s y - x ∈ Λ := by
      have := Λ.add_mem hy' (hang s hs y)
      simpa using this
    let a : Λ := ⟨s y - y, hang s hs y⟩
    have haJ : a ∈ J := ⟨s, hs, y, rfl⟩
    have e : (⟨s y - x, hsy⟩ : Λ) = ⟨y - x, hy'⟩ + a := Subtype.ext (by simp [a])
    rw [hf _ hsy, hf _ hy', e]
    exact (hLf a _ i).trans (by exact_mod_cast hL ⟨a, haJ, rfl⟩)

/-- Part (b): the counting step. -/
theorem isAmenable_IET_of_Q111 (hQ : ∀ (G X : Type) [Group G] [MulAction G X]
      [MulAction.IsPretransitive G X] (S : Finset G),
      (∀ s ∈ S, s⁻¹ ∈ S) → Subgroup.closure (S : Set G) = ⊤ → ∀ x₀ : X,
        HasPolynomialGrowth (S : Set G) x₀ → IsExtensivelyAmenable G X) :
    Garrido.IsAmenable ↥IET := by
  classical
  rw [JMMS.isAmenable_iff_isExtensivelyAmenable_of_le_IET IET le_rfl]
  refine ((JMMS.isExtensivelyAmenable_tfae (G := ↥IET) (X := UnitAddCircle)).out 0 1).mpr ?_
  intro H hH x
  have hHfg : Group.FG ↥H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨S0, hS0⟩ := hHfg.out
  set S1 : Finset ↥H := S0 ∪ S0.image (·⁻¹) with hS1
  have hS1sym : ∀ s ∈ S1, s⁻¹ ∈ S1 := by
    intro s hs
    rw [hS1, Finset.mem_union, Finset.mem_image] at hs ⊢
    rcases hs with hs | ⟨t, ht, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩
    · left; simpa using ht
  have hS1cl : Subgroup.closure (S1 : Set ↥H) = ⊤ := by
    rw [eq_top_iff, ← hS0]
    exact Subgroup.closure_mono (by simp [hS1])
  let φ : ↥H →* Equiv.Perm UnitAddCircle := IET.subtype.comp H.subtype
  set K := φ.range with hK
  set SK : Finset (Equiv.Perm UnitAddCircle) := S1.image φ with hSK
  have hKle : K ≤ IET := by
    rintro _ ⟨h, rfl⟩
    exact (h : ↥IET).2
  have hSKK : ∀ s ∈ SK, s ∈ K := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨t, rfl⟩
  have hSKcl : Subgroup.closure (SK : Set (Equiv.Perm UnitAddCircle)) = K := by
    rw [hSK, Finset.coe_image, ← MonoidHom.map_closure, hS1cl, hK, MonoidHom.range_eq_map]
  obtain ⟨d, f, L, hinj, hL⟩ := exists_embedding_orbit K hKle SK hSKK hSKcl x
  let x₀ : MulAction.orbit (↥H) x := ⟨x, MulAction.mem_orbit_self x⟩
  have hval : ∀ h : ↥H, ((h • x₀ : MulAction.orbit (↥H) x) : UnitAddCircle) = φ h x := fun h => rfl
  have horb : ∀ y : MulAction.orbit (↥H) x, (y : UnitAddCircle) ∈ MulAction.orbit K x := by
    rintro ⟨y, h, rfl⟩
    exact ⟨⟨φ h, h, rfl⟩, rfl⟩
  have hwalk : ∀ l : List ↥H, (∀ s ∈ l, s ∈ (S1 : Set ↥H)) →
      ∀ i, |f (φ l.prod x) i - f x i| ≤ L * l.length := by
    intro l
    induction l with
    | nil => intro _ i; simp
    | cons s l ih =>
      intro hl i
      have h1 := ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) i
      have hy : φ l.prod x ∈ MulAction.orbit K x := ⟨⟨φ l.prod, l.prod, rfl⟩, rfl⟩
      have h2 := hL (φ l.prod x) hy (φ s)
        (Finset.mem_image_of_mem φ (hl s List.mem_cons_self)) i
      rw [List.prod_cons, map_mul, Equiv.Perm.mul_apply, List.length_cons]
      have : |f (φ s (φ l.prod x)) i - f x i| ≤
          |f (φ s (φ l.prod x)) i - f (φ l.prod x) i| + |f (φ l.prod x) i - f x i| := by
        have := abs_add_le (f (φ s (φ l.prod x)) i - f (φ l.prod x) i) (f (φ l.prod x) i - f x i)
        simpa using this
      push_cast
      linarith
  refine hQ (↥H) (MulAction.orbit (↥H) x) S1 hS1sym hS1cl x₀ ⟨(2 * L + 1) ^ d, d, fun n => ?_⟩
  let g : MulAction.orbit (↥H) x → Fin d → ℤ := fun y => f y
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (hinj (horb a) (horb b) hab)
  let B : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun i => Finset.Icc (f x i - L * n) (f x i + L * n)
  have hBcard : B.card = (2 * L * n + 1) ^ d := by
    simp only [B, Fintype.card_piFinset, Int.card_Icc]
    have : ∀ i, f x i + L * n + 1 - (f x i - L * n) = ((2 * L * n + 1 : ℕ) : ℤ) := by
      intro i; push_cast; ring
    simp only [this, Int.toNat_natCast, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ y ∈ schreierBall (S1 : Set ↥H) x₀ n, g y ∈ (B : Set (Fin d → ℤ)) := by
    rintro y ⟨l, hln, hlS, rfl⟩
    simp only [g, B, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := hwalk l hlS i
    rw [hval] at *
    have h2 : (L : ℤ) * l.length ≤ L * n := by
      apply mul_le_mul_of_nonneg_left (by exact_mod_cast hln) (Int.natCast_nonneg _)
    have := abs_le.mp (h1.trans h2)
    constructor <;> linarith [this.1, this.2]
  have hBfin : ((B : Set (Fin d → ℤ))).Finite := B.finite_toSet
  refine ⟨?_, (hBfin.preimage hg.injOn).subset hsub⟩
  calc (schreierBall (S1 : Set ↥H) x₀ n).ncard ≤ B.card := by
        have := Set.ncard_le_ncard_of_injOn g hsub hg.injOn hBfin
        rwa [Set.ncard_coe_finset] at this
    _ = (2 * L * n + 1) ^ d := hBcard
    _ ≤ ((2 * L + 1) * (n + 1)) ^ d := Nat.pow_le_pow_left (by nlinarith) d
    _ = (2 * L + 1) ^ d * (n + 1) ^ d := mul_pow _ _ _

end IETQ

theorem chk_exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth :
    (∀ (G : Subgroup (Equiv.Perm UnitAddCircle)), G ≤ IET →
      ∀ S : Finset (Equiv.Perm UnitAddCircle), (∀ s ∈ S, s ∈ G ∧ s⁻¹ ∈ S) →
        Subgroup.closure (S : Set (Equiv.Perm UnitAddCircle)) = G →
        ∀ x : UnitAddCircle, ∃ (d : ℕ) (f : UnitAddCircle → (Fin d → ℤ)) (C : ℝ),
          Set.InjOn f (MulAction.orbit G x) ∧
            ∀ y ∈ MulAction.orbit G x, ∀ s ∈ S, dist (f (s y)) (f y) ≤ C) ∧
    ((∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (S : Finset G),
      (∀ s ∈ S, s⁻¹ ∈ S) → Subgroup.closure (S : Set G) = ⊤ → ∀ x₀ : X,
        HasPolynomialGrowth (S : Set G) x₀ → IsExtensivelyAmenable G X) →
      Garrido.IsAmenable ↥IET) := by
  refine ⟨fun G hG S hS hcl x => ?_, IETQ.isAmenable_IET_of_Q111⟩
  obtain ⟨d, f, L, hinj, hL⟩ :=
    IETQ.exists_embedding_orbit G hG S (fun s hs => (hS s hs).1) hcl x
  refine ⟨d, f, L, hinj, fun y hy s hs => ?_⟩
  rw [dist_pi_le_iff (Nat.cast_nonneg L)]
  intro i
  rw [Int.dist_eq]
  exact_mod_cast hL y hy s hs i

end JMMS

end

open IntervalExchange
open JMMS in
theorem solution :
    (∀ (G : Subgroup (Equiv.Perm UnitAddCircle)), G ≤ IET →
      ∀ S : Finset (Equiv.Perm UnitAddCircle), (∀ s ∈ S, s ∈ G ∧ s⁻¹ ∈ S) →
        Subgroup.closure (S : Set (Equiv.Perm UnitAddCircle)) = G →
        ∀ x : UnitAddCircle, ∃ (d : ℕ) (f : UnitAddCircle → (Fin d → ℤ)) (C : ℝ),
          Set.InjOn f (MulAction.orbit G x) ∧
            ∀ y ∈ MulAction.orbit G x, ∀ s ∈ S, dist (f (s y)) (f y) ≤ C) ∧
    ((∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (S : Finset G),
      (∀ s ∈ S, s⁻¹ ∈ S) → Subgroup.closure (S : Set G) = ⊤ → ∀ x₀ : X,
        HasPolynomialGrowth (S : Set G) x₀ → IsExtensivelyAmenable G X) →
      Garrido.IsAmenable ↥IET) :=
  JMMS.chk_exists_lipschitz_embedding_and_isAmenable_IET_of_isExtensivelyAmenable_of_hasPolynomialGrowth
