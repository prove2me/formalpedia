-- Prove2me | solution 1 for MazurCampaign.finite_group_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:14.576229+00:00
-- url     : https://prove2.me/submissions/c26e3ef7-a4d5-4288-9ce4-8c480c514945

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from MazurTorsion/GroupTheory/FiniteClassification.lean and
MazurTorsion/GroupTheory/ForbiddenEmbeddings.lean in vilin97/MazurTheorem.
-/
import Definitions.Def_MazurCampaign_group_constraints
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace MazurTorsion
namespace ForbidsEmbedding

variable {A B G H : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup G] [AddCommGroup H]

/-- If `A` embeds in `B` and `A` cannot embed in `G`, then `B` cannot embed in `G`. -/
theorem of_injective_source (h : ForbidsEmbedding A G) (f : A →+ B)
    (hf : Function.Injective f) : ForbidsEmbedding B G := by
  intro g hg
  exact h (g.comp f) (hg.comp hf)

/-- If `G` embeds in `H` and `A` cannot embed in `H`, then `A` cannot embed in `G`. -/
theorem of_injective_target (h : ForbidsEmbedding A H) (f : G →+ H)
    (hf : Function.Injective f) : ForbidsEmbedding A G := by
  intro g hg
  exact h (f.comp g) (hf.comp hg)

/-- Transport the forbidden source along an additive equivalence. -/
theorem addEquiv_source (e : A ≃+ B) :
    ForbidsEmbedding A G ↔ ForbidsEmbedding B G := by
  constructor
  · intro h
    exact h.of_injective_source e.toAddMonoidHom e.injective
  · intro h
    exact h.of_injective_source e.symm.toAddMonoidHom e.symm.injective

/-- Transport the target along an additive equivalence. -/
theorem addEquiv_target (e : G ≃+ H) :
    ForbidsEmbedding A G ↔ ForbidsEmbedding A H := by
  constructor
  · intro h
    exact h.of_injective_target e.symm.toAddMonoidHom e.symm.injective
  · intro h
    exact h.of_injective_target e.toAddMonoidHom e.injective

/-- A forbidden embedding into a group is also forbidden into any additive subgroup. -/
theorem subgroup_target (h : ForbidsEmbedding A G) (K : AddSubgroup G) :
    ForbidsEmbedding A K :=
  h.of_injective_target K.subtype K.subtype_injective

/-- A forbidden embedding rules out an additive equivalence. -/
theorem not_nonempty_addEquiv (h : ForbidsEmbedding A G) :
    ¬ Nonempty (A ≃+ G) := by
  rintro ⟨e⟩
  exact h e.toAddMonoidHom e.injective

end ForbidsEmbedding

end MazurTorsion

namespace MazurTorsion
open MazurCampaign (cyclicOrders)

def allowedBicyclicOrders : Finset ℕ := {2, 4, 6, 8}

def HasMazurGroupShape (G : Type*) [AddCommGroup G] : Prop :=
  (∃ n ∈ cyclicOrders, Nonempty (G ≃+ ZMod n)) ∨
    ∃ n ∈ allowedBicyclicOrders, Nonempty (G ≃+ (ZMod 2 × ZMod n))

private def zmodHomOfElement {A : Type*} [AddCommGroup A] (n : ℕ) (x : A)
    (hx : n • x = 0) : ZMod n →+ A :=
  ZMod.lift n
    ⟨
      { toFun := fun z : ℤ => z • x
        map_zero' := zero_zsmul x
        map_add' := fun a b => add_zsmul x a b },
      by simpa using hx⟩

private theorem zmodHomOfElement_injective {A : Type*} [AddCommGroup A] (n : ℕ) (x : A)
    (hx : n • x = 0) (horder : addOrderOf x = n) :
    Function.Injective (zmodHomOfElement n x hx) := by
  change Function.Injective (ZMod.lift n _)
  rw [ZMod.lift_injective]
  intro m hm
  change m • x = 0 at hm
  apply (CharP.intCast_eq_zero_iff (ZMod n) n m).2
  rw [← horder]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hm

private theorem exists_zmod_embedding_of_dvd {d n : ℕ} (hd : d ∣ n) (_hdpos : 0 < d)
    (hn : n ≠ 0) :
    ∃ f : ZMod d →+ ZMod n, Function.Injective f := by
  let x : ZMod n := (n / d : ℕ)
  have hxorder : addOrderOf x = d := by
    rw [ZMod.addOrderOf_coe (n / d) hn, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
      Nat.div_div_self hd hn]
  have hx : d • x = 0 := (addOrderOf_dvd_iff_nsmul_eq_zero.mp (hxorder ▸ dvd_rfl))
  exact ⟨zmodHomOfElement d x hx, zmodHomOfElement_injective d x hx hxorder⟩

private def directSumCoordinateHom
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j)) :
    DirectSum κ A →+ DirectSum ι B :=
  DirectSum.toAddMonoid fun j => (DirectSum.of B (s j)).comp (f j)

private theorem directSumCoordinateHom_apply
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j))
    (x : DirectSum κ A) (j : κ) :
    directSumCoordinateHom A B s f x (s j) = f j (x j) := by
  induction x using DirectSum.induction_on with
  | zero => simp [directSumCoordinateHom]
  | of i x =>
      by_cases hij : i = j
      · subst i
        simp [directSumCoordinateHom]
      · have hsij : s i ≠ s j := fun h => hij (s.injective h)
        rw [directSumCoordinateHom, DirectSum.toAddMonoid_of]
        change ((DirectSum.of B (s i)) (f i x)) (s j) =
          f j (((DirectSum.of A i) x) j)
        rw [DirectSum.of_apply, DirectSum.of_apply]
        simp [hij, hsij]
  | add x y hx hy =>
      rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

private theorem directSumCoordinateHom_injective
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j))
    (hf : ∀ j, Function.Injective (f j)) :
    Function.Injective (directSumCoordinateHom A B s f) := by
  intro x y hxy
  apply DFinsupp.ext
  intro j
  apply hf j
  rw [← directSumCoordinateHom_apply A B s f x j,
    ← directSumCoordinateHom_apply A B s f y j, hxy]

private theorem exists_pi_zmod_embedding_of_factors
    {G : Type*} [AddCommGroup G] {κ ι : Type*} [Finite κ]
    (d : κ → ℕ) (n : ι → ℕ) (s : κ ↪ ι)
    (hd : ∀ j, d j ∣ n (s j)) (hdpos : ∀ j, 0 < d j) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i)) :
    ∃ f : (∀ j, ZMod (d j)) →+ G, Function.Injective f := by
  classical
  letI := Fintype.ofFinite κ
  choose fj hfj using fun j => exists_zmod_embedding_of_dvd (hd j) (hdpos j) (hn (s j))
  let coordinates :
      DirectSum κ (fun j => ZMod (d j)) →+ DirectSum ι (fun i => ZMod (n i)) :=
    directSumCoordinateHom (fun j => ZMod (d j)) (fun i => ZMod (n i)) s fj
  let f : (∀ j, ZMod (d j)) →+ G :=
    e.symm.toAddMonoidHom.comp <|
      coordinates.comp (DirectSum.addEquivProd (fun j => ZMod (d j))).symm.toAddMonoidHom
  have hcoordinates : Function.Injective coordinates := by
    dsimp only [coordinates]
    exact directSumCoordinateHom_injective (fun j => ZMod (d j))
      (fun i => ZMod (n i)) s fj hfj
  refine ⟨f, ?_⟩
  intro x y hxy
  apply (DirectSum.addEquivProd (fun j => ZMod (d j))).symm.injective
  apply hcoordinates
  apply e.symm.injective
  exact hxy

/-- If a finite elementary-divisor presentation has at least `k` factors divisible by `d`, then
`(ZMod d) ^ k` embeds.  Consequently a forbidden elementary abelian subgroup bounds the number
of such factors. -/
theorem factor_count_lt_of_forbidden_pi
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d k : ℕ} (hdpos : 0 < d) (hforbid : ForbidsEmbedding (Fin k → ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < k := by
  classical
  by_contra hcount
  rw [not_lt] at hcount
  have hcard :
      Fintype.card (Fin k) ≤ Fintype.card {i : ι // d ∣ n i} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact hcount
  obtain ⟨s₀⟩ := Function.Embedding.nonempty_of_card_le hcard
  let s : Fin k ↪ ι := s₀.trans (Function.Embedding.subtype fun i : ι => d ∣ n i)
  have hs : ∀ j, d ∣ n (s j) := fun j => (s₀ j).2
  obtain ⟨f, hf⟩ := exists_pi_zmod_embedding_of_factors
    (fun _ : Fin k => d) n s hs (fun _ => hdpos) hn e
  exact hforbid f hf

/-- A square-subgroup exclusion says that at most one elementary-divisor factor is divisible by
`d`. -/
theorem factor_count_lt_two_of_forbidden_square
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d : ℕ} (hdpos : 0 < d) (hforbid : ForbidsEmbedding (ZMod d × ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < 2 := by
  let epi : (Fin 2 → ZMod d) ≃+ (ZMod d × ZMod d) :=
    (LinearEquiv.piFinTwo ℤ fun _ : Fin 2 => ZMod d).toAddEquiv
  exact factor_count_lt_of_forbidden_pi n hn e hdpos
    ((ForbidsEmbedding.addEquiv_source epi).mpr hforbid)

private def piFinThreeAddEquiv (A : Type*) [AddCommGroup A] :
    (Fin 3 → A) ≃+ (A × A × A) :=
  let e₁ : (Fin 3 → A) ≃ₗ[ℤ] (Option (Fin 2) → A) :=
    LinearEquiv.piCongrLeft ℤ (fun _ : Option (Fin 2) => A) (finSuccEquiv 2)
  let e₂ : (Option (Fin 2) → A) ≃ₗ[ℤ] (A × (Fin 2 → A)) :=
    LinearEquiv.piOptionEquivProd ℤ
  let e₃ : (A × (Fin 2 → A)) ≃ₗ[ℤ] (A × A × A) :=
    (LinearEquiv.refl ℤ A).prodCongr
      (LinearEquiv.piFinTwo ℤ fun _ : Fin 2 => A)
  (e₁.trans <| e₂.trans e₃).toAddEquiv

/-- A cube-subgroup exclusion says that at most two elementary-divisor factors are divisible by
`d`. -/
theorem factor_count_lt_three_of_forbidden_cube
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d : ℕ} (hdpos : 0 < d)
    (hforbid : ForbidsEmbedding (ZMod d × ZMod d × ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < 3 :=
  factor_count_lt_of_forbidden_pi n hn e hdpos
    ((ForbidsEmbedding.addEquiv_source (piFinThreeAddEquiv (ZMod d))).mpr hforbid)

private theorem square_embeds_of_dvd {G : Type*} [AddCommGroup G] {d m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) (hdm : d ∣ m) (hdn : d ∣ n) (hdpos : 0 < d)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ f : ZMod d × ZMod d →+ G, Function.Injective f := by
  obtain ⟨fm, hfm⟩ := exists_zmod_embedding_of_dvd hdm hdpos hm
  obtain ⟨fn, hfn⟩ := exists_zmod_embedding_of_dvd hdn hdpos hn
  let f : ZMod d × ZMod d →+ G :=
    e.symm.toAddMonoidHom.comp (fm.prodMap fn)
  exact ⟨f, e.symm.injective.comp (hfm.prodMap hfn)⟩

private theorem left_factor_order {G : Type*} [AddCommGroup G] {m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) :
    addOrderOf (e.symm (1, 0)) = m := by
  calc
    addOrderOf (e.symm (1, 0)) = addOrderOf ((1, 0) : ZMod m × ZMod n) := by
      simp
    _ = addOrderOf (1 : ZMod m) := by
      exact addOrderOf_injective (AddMonoidHom.inl (ZMod m) (ZMod n))
        (fun _ _ h => congrArg Prod.fst h) 1
    _ = m := ZMod.addOrderOf_one m

private theorem right_factor_order {G : Type*} [AddCommGroup G] {m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) :
    addOrderOf (e.symm (0, 1)) = n := by
  calc
    addOrderOf (e.symm (0, 1)) = addOrderOf ((0, 1) : ZMod m × ZMod n) := by
      simp
    _ = addOrderOf (1 : ZMod n) := by
      exact addOrderOf_injective (AddMonoidHom.inr (ZMod m) (ZMod n))
        (fun _ _ h => congrArg Prod.snd h) 1
    _ = n := ZMod.addOrderOf_one n

private theorem no_square_dvd {G : Type*} [AddCommGroup G] {d m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) (hforbid : ForbidsEmbedding (ZMod d × ZMod d) G)
    (hdm : d ∣ m) (hdn : d ∣ n) (hdpos : 0 < d) (hm : m ≠ 0) (hn : n ≠ 0) :
    False := by
  obtain ⟨f, hf⟩ := square_embeds_of_dvd e hdm hdn hdpos hm hn
  exact hforbid f hf

/-- The pure rank-two finite-abelian reduction behind Mazur's classification.

The hypotheses say that `G` has invariant factors `m ∣ n`, every element of `G` has one of
Mazur's allowed point orders, and the seven standard obstruction groups do not embed.  The
conclusion is precisely Mazur's cyclic/bicyclic list.
-/
theorem hasMazurGroupShape_of_rankTwo
    {G : Type*} [AddCommGroup G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G)
    {m n : ℕ} (hmn : m ∣ n) (e : G ≃+ (ZMod m × ZMod n)) :
    HasMazurGroupShape G := by
  have hm : m ∈ cyclicOrders := by
    simpa [left_factor_order e] using horders (e.symm (1, 0))
  have hn : n ∈ cyclicOrders := by
    simpa [right_factor_order e] using horders (e.symm (0, 1))
  have hnzero : n ≠ 0 := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hm_cases :
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
        m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 12 := by
    simpa only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    refine ⟨n, hn, ?_⟩
    exact ⟨e.trans AddEquiv.uniqueProd⟩
  · right
    have hn_cases :
        n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
      have hn_all :
          n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
            n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 := by
        simpa only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] using hn
      rcases hn_all with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all
    rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨4, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨6, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨8, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact (havoid.c2c10 e.symm.toAddMonoidHom e.symm.injective).elim
    · exact (havoid.c2c12 e.symm.toAddMonoidHom e.symm.injective).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c4Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c5Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c7Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c4Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c5Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim

/-- The rank-two finite-abelian reduction immediately gives the numerical bound needed by the
LeanPool challenge. -/
theorem card_le_sixteen_of_rankTwo
    {G : Type*} [AddCommGroup G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G)
    {m n : ℕ} (hmn : m ∣ n) (e : G ≃+ (ZMod m × ZMod n)) :
    Nat.card G ≤ 16 := by
  rcases hasMazurGroupShape_of_rankTwo horders havoid hmn e with
    ⟨k, hk, ⟨ek⟩⟩ | ⟨k, hk, ⟨ek⟩⟩
  · rw [Nat.card_congr ek.toEquiv, Nat.card_zmod]
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  · rw [Nat.card_congr ek.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
    simp only [allowedBicyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hk
    omega

private theorem prime_pow_dvd_allowed_order_cases
    {p a D : ℕ} (hp : p.Prime) (hD : D ∈ cyclicOrders) (hdiv : p ^ a ∣ D) :
    p ^ a = 1 ∨ p ^ a = 2 ∨ p ^ a = 3 ∨ p ^ a = 4 ∨
      p ^ a = 5 ∨ p ^ a = 7 ∨ p ^ a = 8 ∨ p ^ a = 9 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hDpos : 0 < D := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD
    omega
  have hDle : D ≤ 12 := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD
    omega
  have hqle : p ^ a ≤ D := Nat.le_of_dvd hDpos hdiv
  have ha : a < 4 := by
    by_contra ha
    rw [not_lt] at ha
    have h₁ : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have h₂ : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
    norm_num at h₁
    omega
  have hple : p ≤ 12 := by
    exact (Nat.le_of_dvd (pow_pos hp.pos a) (dvd_pow_self p ha0)).trans
      (hqle.trans hDle)
  have hpcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    rcases hp.eq_two_or_odd with hp2 | hpodd
    · exact Or.inl hp2
    have hpne9 : p ≠ 9 := by
      intro hp9
      subst p
      rcases hp.eq_one_or_self_of_dvd 3 (by norm_num) with h | h <;> omega
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p <;> omega
  rcases hpcases with rfl | rfl | rfl | rfl | rfl <;>
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD <;>
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases a <;> norm_num at hdiv <;> norm_num

/-- Allowed element orders and the four elementary rank obstructions put a finite abelian
group in rank-two invariant-factor form. -/
theorem exists_rankTwoPresentation_of_allowed_orders_and_forbidden
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (h2rank : ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) G)
    (h3rank : ForbidsEmbedding (ZMod 3 × ZMod 3) G)
    (h5rank : ForbidsEmbedding (ZMod 5 × ZMod 5) G)
    (h7rank : ForbidsEmbedding (ZMod 7 × ZMod 7) G) :
    ∃ m n : ℕ, m ∣ n ∧ Nonempty (G ≃+ (ZMod m × ZMod n)) := by
  classical
  obtain ⟨ι, hι, p, hp, a, ⟨e₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite G
  letI : Fintype ι := hι
  let q : ι → ℕ := fun i => p i ^ a i
  let e : G ≃+ DirectSum ι (fun i => ZMod (q i)) := e₀
  let eprod : G ≃+ (∀ i, ZMod (q i)) :=
    e.trans (DirectSum.addEquivProd fun i => ZMod (q i))
  let ones : ∀ i, ZMod (q i) := fun _ => 1
  let x : G := eprod.symm ones
  let D : ℕ := addOrderOf x
  have hD : D ∈ cyclicOrders := horders x
  have horder : addOrderOf ones = D := by simp [D, x]
  have hdiv : ∀ i, q i ∣ D := by
    intro i
    have hi := addOrderOf_map_dvd (Pi.evalAddMonoidHom (fun i => ZMod (q i)) i) ones
    change addOrderOf (ones i) ∣ addOrderOf ones at hi
    rwa [show addOrderOf (ones i) = q i by simp [ones, ZMod.addOrderOf_one], horder] at hi
  have hq :
      ∀ i, q i = 1 ∨ q i = 2 ∨ q i = 3 ∨ q i = 4 ∨
        q i = 5 ∨ q i = 7 ∨ q i = 8 ∨ q i = 9 := by
    intro i
    exact prime_pow_dvd_allowed_order_cases (hp i) hD (hdiv i)
  have hn : ∀ i, q i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  have hc2 := factor_count_lt_three_of_forbidden_cube q hn e (by norm_num) h2rank
  have hc3 := factor_count_lt_two_of_forbidden_square q hn e (by norm_num) h3rank
  have hc5 := factor_count_lt_two_of_forbidden_square q hn e (by norm_num) h5rank
  have hc7 := factor_count_lt_two_of_forbidden_square q hn e (by norm_num) h7rank
  have factor_unique (d : ℕ)
      (hc : (Finset.univ.filter fun i => d ∣ q i).card < 2)
      {i j : ι} (hi : d ∣ q i) (hj : d ∣ q j) : i = j := by
    apply (Finset.card_le_one.mp (show
      (Finset.univ.filter fun i => d ∣ q i).card ≤ 1 by omega)) i
    · simp [hi]
    · simp [hj]
  have prime_cases_of_dvd {r : ℕ} (hr : r.Prime) {i : ι} (hri : r ∣ q i) :
      r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
    have hqle : q i ≤ 9 := by
      rcases hq i with h | h | h | h | h | h | h | h <;> omega
    have hrle : r ≤ q i := Nat.le_of_dvd (by exact Nat.pos_of_ne_zero (hn i)) hri
    have hrle9 : r ≤ 9 := hrle.trans hqle
    have hr2 := hr.two_le
    interval_cases r
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact ((by decide : ¬Nat.Prime 4) hr).elim
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact ((by decide : ¬Nat.Prime 6) hr).elim
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact ((by decide : ¬Nat.Prime 8) hr).elim
    · exact ((by decide : ¬Nat.Prime 9) hr).elim
  have pairwise_of_two_unique
      (hc : (Finset.univ.filter fun i => 2 ∣ q i).card < 2) :
      Pairwise (Function.onFun Nat.Coprime q) := by
    intro i j hij
    by_contra hcop
    obtain ⟨r, hr, hri, hrj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    rcases prime_cases_of_dvd hr hri with rfl | rfl | rfl | rfl
    · exact hij (factor_unique 2 hc hri hrj)
    · exact hij (factor_unique 3 hc3 hri hrj)
    · exact hij (factor_unique 5 hc5 hri hrj)
    · exact hij (factor_unique 7 hc7 hri hrj)
  have even_factor_cases {i : ι} (hi : 2 ∣ q i) :
      q i = 2 ∨ q i = 4 ∨ q i = 8 := by
    rcases hq i with h | h | h | h | h | h | h | h
    · norm_num [h] at hi
    · exact Or.inl h
    · norm_num [h] at hi
    · exact Or.inr (Or.inl h)
    · norm_num [h] at hi
    · norm_num [h] at hi
    · exact Or.inr (Or.inr h)
    · norm_num [h] at hi
  by_cases hc : (Finset.univ.filter fun i => 2 ∣ q i).card < 2
  · let n := ∏ i, q i
    let ez : ZMod n ≃+ (∀ i, ZMod (q i)) :=
      (ZMod.prodEquivPi q (pairwise_of_two_unique hc)).toAddEquiv
    refine ⟨1, n, one_dvd n, ⟨eprod.trans <| ez.symm.trans AddEquiv.uniqueProd.symm⟩⟩
  · have hc_eq : (Finset.univ.filter fun i => 2 ∣ q i).card = 2 := by omega
    obtain ⟨i, j, hij, hfilter⟩ := Finset.card_eq_two.mp hc_eq
    have hi2 : 2 ∣ q i := by
      have : i ∈ Finset.univ.filter fun k => 2 ∣ q k := by rw [hfilter]; simp
      simpa using (Finset.mem_filter.mp this).2
    have hj2 : 2 ∣ q j := by
      have : j ∈ Finset.univ.filter fun k => 2 ∣ q k := by rw [hfilter]; simp
      simpa using (Finset.mem_filter.mp this).2
    have hcomparable : q i ∣ q j ∨ q j ∣ q i := by
      rcases even_factor_cases hi2 with hi | hi | hi <;>
        rcases even_factor_cases hj2 with hj | hj | hj
      all_goals norm_num [hi, hj]
    have heven : ∀ {k : ι}, 2 ∣ q k → k = i ∨ k = j := by
      intro k hk
      have hmem : k ∈ Finset.univ.filter fun l => 2 ∣ q l := by simp [hk]
      rw [hfilter] at hmem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have finish {i j : ι} (hij : i ≠ j) (hijdiv : q i ∣ q j)
        (heven : ∀ {k : ι}, 2 ∣ q k → k = i ∨ k = j) :
        ∃ m n : ℕ, m ∣ n ∧ Nonempty (G ≃+ (ZMod m × ZMod n)) := by
      let κ := {k : ι // k ≠ i}
      let r : κ → ℕ := fun k => q k.1
      have hrpair : Pairwise (Function.onFun Nat.Coprime r) := by
        intro k l hkl
        by_contra hcop
        obtain ⟨d, hd, hdk, hdl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
        rcases prime_cases_of_dvd hd hdk with rfl | rfl | rfl | rfl
        · rcases heven hdk with hki | hkj
          · exact k.2 hki
          · rcases heven hdl with hli | hlj
            · exact l.2 hli
            · exact hkl (Subtype.ext (hkj.trans hlj.symm))
        · exact hkl (Subtype.ext (factor_unique 3 hc3 hdk hdl))
        · exact hkl (Subtype.ext (factor_unique 5 hc5 hdk hdl))
        · exact hkl (Subtype.ext (factor_unique 7 hc7 hdk hdl))
      let n := ∏ k : κ, r k
      let esplit : (∀ k : ι, ZMod (q k)) ≃+ (ZMod (q i) × (∀ k : κ, ZMod (r k))) := by
        let eidx : Option κ ≃ ι := Equiv.optionSubtypeNe i
        let e₁ := (LinearEquiv.piCongrLeft ℤ (fun k : ι => ZMod (q k)) eidx).symm
        let e₂ := LinearEquiv.piOptionEquivProd
          (M := fun o => ZMod (q (eidx o))) ℤ
        exact (e₁.trans e₂).toAddEquiv
      let ez : ZMod n ≃+ (∀ k : κ, ZMod (r k)) :=
        (ZMod.prodEquivPi r hrpair).toAddEquiv
      let en : G ≃+ (ZMod (q i) × ZMod n) :=
        eprod.trans <| esplit.trans (AddEquiv.prodCongr (AddEquiv.refl _) ez.symm)
      have hjκ : (⟨j, hij.symm⟩ : κ) ∈ Finset.univ := Finset.mem_univ _
      have hjdvd : q j ∣ n := by
        exact Finset.dvd_prod_of_mem (fun k : κ => r k) hjκ
      exact ⟨q i, n, dvd_trans hijdiv hjdvd, ⟨en⟩⟩
    rcases hcomparable with hijdiv | hjidiv
    · exact finish hij hijdiv heven
    · exact finish hij.symm hjidiv fun hk => (heven hk).symm

/-- If every element of a finite abelian group has a Mazur-allowed order and none of the seven
standard obstruction groups embeds, then the group has at most sixteen elements. -/
theorem card_le_sixteen_of_allowed_orders_and_forbidden
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G) :
    Nat.card G ≤ 16 := by
  obtain ⟨m, n, hmn, ⟨e⟩⟩ :=
    exists_rankTwoPresentation_of_allowed_orders_and_forbidden horders
      havoid.c2Cube havoid.c3Square havoid.c5Square havoid.c7Square
  exact card_le_sixteen_of_rankTwo horders havoid hmn e

end MazurTorsion

open MazurTorsion in
theorem solution
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ MazurCampaign.cyclicOrders)
    (havoid : MazurTorsion.AvoidsMazurForbiddenSubgroups G) :
    (∃ n ∈ MazurCampaign.cyclicOrders, Nonempty (G ≃+ ZMod n)) ∨
      ∃ m ∈ MazurCampaign.bicyclicParameters,
        Nonempty (G ≃+ (ZMod 2 × ZMod (2 * m))) := by
  obtain ⟨m, n, hmn, ⟨e⟩⟩ :=
    exists_rankTwoPresentation_of_allowed_orders_and_forbidden horders
      havoid.c2Cube havoid.c3Square havoid.c5Square havoid.c7Square
  rcases hasMazurGroupShape_of_rankTwo horders havoid hmn e with
    ⟨n, hn, he⟩ | ⟨n, hn, he⟩
  · exact Or.inl ⟨n, hn, he⟩
  · right
    simp only [allowedBicyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp [MazurCampaign.bicyclicParameters], by simpa using he⟩
    · exact ⟨2, by simp [MazurCampaign.bicyclicParameters], by simpa using he⟩
    · exact ⟨3, by simp [MazurCampaign.bicyclicParameters], by simpa using he⟩
    · exact ⟨4, by simp [MazurCampaign.bicyclicParameters], by simpa using he⟩

#print axioms solution
