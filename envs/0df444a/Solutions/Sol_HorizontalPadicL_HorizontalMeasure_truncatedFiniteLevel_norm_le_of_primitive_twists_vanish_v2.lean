-- Prove2me | solution 1 for HorizontalPadicL.HorizontalMeasure.truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:11:23.271434+00:00
-- url     : https://prove2.me/submissions/de7853fc-b7af-4d6d-8d51-4d85fd94b6b7

import Definitions.Def_KN_TruncatedHorizontalCoefficientsV2
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

-- CharacterDescent
set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Coordinate reduction as a group homomorphism. -/
def truncateHorizontalCoordinatesHom {p : ℕ} {e : ℕ → ℕ} (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    HorizontalFiniteGroup p e A →* HorizontalFiniteGroup p (fun _ ↦ m) A where
  toFun := truncateHorizontalCoordinates m he A
  map_one' := by
    funext i
    exact congrArg Multiplicative.ofAdd (map_zero (ZMod.castHom (pow_dvd_pow p (he i.1)) (ZMod (p ^ m))))
  map_mul' x y := by
    funext i
    exact congrArg Multiplicative.ofAdd (map_add (ZMod.castHom (pow_dvd_pow p (he i.1)) (ZMod (p ^ m))) _ _)

@[simp] theorem truncateHorizontalCoordinatesHom_apply {p : ℕ} {e : ℕ → ℕ} (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) (x : HorizontalFiniteGroup p e A) :
    truncateHorizontalCoordinatesHom m he A x = truncateHorizontalCoordinates m he A x := rfl

theorem truncateHorizontalCoordinates_surjective {p : ℕ} {e : ℕ → ℕ} (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    Function.Surjective (truncateHorizontalCoordinates (p := p) m he A) := by
  intro y
  choose x hx using fun i : {n : ℕ // n ∈ A} ↦
    ZMod.castHom_surjective (pow_dvd_pow p (he i.1)) (y i).toAdd
  exact ⟨fun i ↦ Multiplicative.ofAdd (x i), funext fun i ↦ congrArg Multiplicative.ofAdd (hx i)⟩

theorem truncateHorizontalCoordinates_ker_pow {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ}
    (m : ℕ) (he : ∀ n, m ≤ e n) (A : Finset ℕ) (x : HorizontalFiniteGroup p e A)
    (hx : truncateHorizontalCoordinates m he A x = 1) :
    ∃ y : HorizontalFiniteGroup p e A, y ^ (p ^ m) = x := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero _ hp⟩
  have hd (i : {n : ℕ // n ∈ A}) : p ^ m ∣ (x i).toAdd.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hi := congrArg (fun z ↦ (z i).toAdd) hx
    change ZMod.castHom (pow_dvd_pow p (he i.1)) (ZMod (p ^ m)) (x i).toAdd = 0 at hi
    simpa only [ZMod.castHom_apply, ZMod.natCast_val] using hi
  refine ⟨fun i ↦ Multiplicative.ofAdd (((x i).toAdd.val / p ^ m : ℕ) : ZMod (p ^ e i.1)), ?_⟩
  funext i
  change (p ^ m) • (((x i).toAdd.val / p ^ m : ℕ) : ZMod (p ^ e i.1)) = (x i).toAdd
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hd i), ZMod.natCast_zmod_val]

theorem horizontalFiniteGroup_pow_eq_one {p m : ℕ} (A : Finset ℕ)
    (x : HorizontalFiniteGroup p (fun _ ↦ m) A) : x ^ (p ^ m) = 1 := by
  funext i
  change (p ^ m) • (x i).toAdd = 0
  simp [nsmul_eq_mul]

/-- The canonical inclusion of roots of unity into the coefficient field. -/
def rootsOfUnityValue (p q : ℕ) [Fact p.Prime] : rootsOfUnity q ℂ_[p] →* ℂ_[p] :=
  (Units.coeHom ℂ_[p]).comp (rootsOfUnity q ℂ_[p]).subtype

/-- Regard a character of bounded order as a root-valued character. -/
def characterToRoots {p q : ℕ} [Fact p.Prime] [NeZero q] {G : Type*} [Monoid G]
    (χ : G →* ℂ_[p]) (hχ : χ ^ q = 1) : G →* rootsOfUnity q ℂ_[p] where
  toFun x := rootsOfUnity.mkOfPowEq (χ x) (by simpa using DFunLike.congr_fun hχ x)
  map_one' := by apply rootsOfUnity.coe_injective; simp
  map_mul' x y := by apply rootsOfUnity.coe_injective; simp

@[simp] theorem characterToRoots_value {p q : ℕ} [Fact p.Prime] [NeZero q]
    {G : Type*} [Monoid G] (χ : G →* ℂ_[p]) (hχ : χ ^ q = 1) (x : G) :
    rootsOfUnityValue p q (characterToRoots χ hχ x) = χ x := rfl

/-- A bounded-order character factors through coordinate reduction. -/
theorem HorizontalCharacter.exists_truncated_roots {p : ℕ} [Fact p.Prime]
    {e : ℕ → ℕ} (m : ℕ) (he : ∀ n, m ≤ e n) (χ : HorizontalCharacter p e)
    (hχ : χ.toMonoidHom ^ (p ^ m) = 1) :
    ∃ ψ : HorizontalFiniteGroup p (fun _ ↦ m) χ.support →* rootsOfUnity (p ^ m) ℂ_[p],
      (rootsOfUnityValue p (p ^ m)).comp
        (ψ.comp (truncateHorizontalCoordinatesHom m he χ.support)) = χ.toMonoidHom := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let φ := characterToRoots χ.toMonoidHom hχ
  let f := truncateHorizontalCoordinatesHom (p := p) m he χ.support
  have hf : Function.Surjective f := truncateHorizontalCoordinates_surjective m he χ.support
  have hk : f.ker ≤ φ.ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := truncateHorizontalCoordinates_ker_pow m he χ.support x hx
    apply rootsOfUnity.coe_injective
    change χ.toMonoidHom (y ^ (p ^ m)) = 1
    rw [map_pow]
    exact DFunLike.congr_fun hχ y
  refine ⟨f.liftOfSurjective hf ⟨φ, hk⟩, ?_⟩
  apply MonoidHom.ext
  intro x
  change rootsOfUnityValue p (p ^ m)
    ((f.liftOfSurjective hf ⟨φ, hk⟩) (f x)) = χ.toMonoidHom x
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- A character of exact order `p ^ m` factors through coordinate reduction. -/
theorem HorizontalCharacter.exists_truncated {p : ℕ} [Fact p.Prime]
    {e : ℕ → ℕ} (m : ℕ) (he : ∀ n, m ≤ e n) (χ : HorizontalCharacter p e)
    (hχ : orderOf χ.toMonoidHom = p ^ m) :
    ∃ ψ : HorizontalFiniteGroup p (fun _ ↦ m) χ.support →* ℂ_[p],
      ψ.comp (truncateHorizontalCoordinatesHom m he χ.support) = χ.toMonoidHom := by
  obtain ⟨ψ, hψ⟩ := χ.exists_truncated_roots m he (hχ ▸ pow_orderOf_eq_one χ.toMonoidHom)
  exact ⟨(rootsOfUnityValue p (p ^ m)).comp ψ, hψ⟩

/-- A finite character on the truncated coordinates defines a horizontal character. -/
def HorizontalCharacter.ofTruncated {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ}
    (m : ℕ) (he : ∀ n, m ≤ e n) (A : Finset ℕ)
    (ψ : HorizontalFiniteGroup p (fun _ ↦ m) A →* ℂ_[p]) : HorizontalCharacter p e where
  support := A
  toMonoidHom := ψ.comp (truncateHorizontalCoordinatesHom m he A)

theorem HorizontalCharacter.ofTruncated_order_dvd {p : ℕ} [Fact p.Prime]
    {e : ℕ → ℕ} (m : ℕ) (he : ∀ n, m ≤ e n) (A : Finset ℕ)
    (ψ : HorizontalFiniteGroup p (fun _ ↦ m) A →* ℂ_[p]) :
    orderOf (HorizontalCharacter.ofTruncated m he A ψ).toMonoidHom ∣ p ^ m := by
  apply orderOf_dvd_of_pow_eq_one
  apply MonoidHom.ext
  intro x
  change ψ (truncateHorizontalCoordinatesHom m he A x) ^ (p ^ m) = 1
  rw [← map_pow, horizontalFiniteGroup_pow_eq_one, map_one]

end HorizontalPadicL

end

-- HorizontalTransport
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

theorem HorizontalMeasure.truncatedFiniteLevel_compatible
    {R : Type*} [CommRing R] {p : ℕ} {e : ℕ → ℕ}
    (μ : HorizontalMeasure R p e) (m : ℕ) (he : ∀ n, m ≤ e n)
    {A D : Finset ℕ} (hAD : A ⊆ D) :
    Finsupp.mapDomain (restrictHorizontalCoordinates hAD)
      (μ.truncatedFiniteLevel m he D) = μ.truncatedFiniteLevel m he A := by
  unfold HorizontalMeasure.truncatedFiniteLevel
  rw [← Finsupp.mapDomain_comp]
  have hcomm : restrictHorizontalCoordinates (p := p) (m := fun _ ↦ m) hAD ∘
      truncateHorizontalCoordinates m he D =
      truncateHorizontalCoordinates m he A ∘ restrictHorizontalCoordinates hAD := rfl
  rw [hcomm, Finsupp.mapDomain_comp]
  congr 1
  exact μ.compatible A D hAD

theorem HorizontalMeasure.eval_eq_sum_of_support_subset
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (χ : HorizontalCharacter p e)
    {D : Finset ℕ} (hD : χ.support ⊆ D) :
    μ.eval χ = (μ.finiteLevel D).sum
      (fun g a ↦ (a : ℂ_[p]) * χ.toMonoidHom (restrictHorizontalCoordinates hD g)) := by
  unfold HorizontalMeasure.eval
  rw [← μ.compatible χ.support D hD]
  change (Finsupp.mapDomain _ _).sum _ = _
  exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [add_mul])

theorem HorizontalMeasure.truncatedFiniteLevel_eval
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (m : ℕ) (he : ∀ n, m ≤ e n)
    (A : Finset ℕ) (η : HorizontalFiniteGroup p (fun _ ↦ m) A → ℂ_[p]) :
    (μ.truncatedFiniteLevel m he A).sum (fun g a ↦ (a : ℂ_[p]) * η g) =
      (μ.finiteLevel A).sum
        (fun g a ↦ (a : ℂ_[p]) * η (truncateHorizontalCoordinates m he A g)) := by
  exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [add_mul])

theorem norm_mapDomain_apply_le
    {p : ℕ} [Fact p.Prime] {R : Subring ℂ_[p]} {α β : Type*}
    (l : α →₀ R) (f : α → β) (B : ℝ) (hB : 0 ≤ B)
    (hl : ∀ a, ‖(l a : ℂ_[p])‖ ≤ B) (b : β) :
    ‖(Finsupp.mapDomain f l b : ℂ_[p])‖ ≤ B := by
  classical
  have heq : Finsupp.mapDomain f l b =
      ∑ a ∈ l.support, if f a = b then l a else 0 := by
    simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
  rw [heq]
  change ‖R.subtype (∑ a ∈ l.support, if f a = b then l a else 0)‖ ≤ B
  rw [map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro a ha
  split_ifs <;> simp_all

theorem mapDomain_fst_apply
    {R : Type*} [AddCommMonoid R] {α β : Type*} [Fintype α] [Fintype β]
    (l : α × β →₀ R) (a : α) :
    Finsupp.mapDomain Prod.fst l a = ∑ b, l (a, b) := by
  classical
  simp only [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, Finsupp.single_apply]
  rw [Finset.sum_comm]
  simp

theorem mapDomain_sum_mul
    {p : ℕ} [Fact p.Prime] {R : Subring ℂ_[p]} {α β : Type*} [Fintype β]
    (l : α →₀ R) (f : α → β) (η : β → ℂ_[p]) :
    (∑ b, (Finsupp.mapDomain f l b : ℂ_[p]) * η b) =
      l.sum (fun a c ↦ (c : ℂ_[p]) * η (f a)) := by
  rw [← (Finsupp.mapDomain f l).sum_fintype (fun b c ↦ (c : ℂ_[p]) * η b)
    (fun _ ↦ by simp)]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ by simp [add_mul])

end HorizontalPadicL

end

-- OrbitNorm
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Sum a function constant on right subgroup translates by choosing one representative per coset. -/
lemma sum_eq_card_mul_quotient_sum {G : Type*} [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)] {K : Type*} [CommRing K] (f : G → K)
    (hf : ∀ g (h : S), f (g * h) = f g) :
    ∑ g, f g = (Fintype.card S : K) * ∑ q : G ⧸ S, f q.out := by
  classical
  let a : (G ⧸ S) × S → G := fun x ↦ x.1.out * x.2
  have ha (x : (G ⧸ S) × S) : QuotientGroup.mk (a x) = x.1 := by
    simp [a, QuotientGroup.mk_mul_of_mem _ x.2.property]
  have hab : Function.Bijective a := by
    constructor
    · rintro ⟨q₁, s₁⟩ ⟨q₂, s₂⟩ h
      have hq : q₁ = q₂ := (ha _).symm.trans ((congrArg QuotientGroup.mk h).trans (ha _))
      subst q₂
      have hs : s₁ = s₂ := Subtype.ext (mul_left_cancel h)
      subst s₂
      rfl
    · intro g
      refine ⟨(QuotientGroup.mk g,
        ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹ * g, ?_⟩), ?_⟩
      · exact QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk g))
      · simp [a]
  let e := Equiv.ofBijective a hab
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  change (∑ q : G ⧸ S, ∑ s : S, f (q.out * s)) = _
  simp_rw [hf]
  simp [Finset.mul_sum, nsmul_eq_mul]

/-- Invariance under a subgroup of order `p` improves a uniform `p`-adic bound by `1 / p`. -/
lemma subgroup_invariant_sum_norm_le {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (S : Subgroup G) (hS : Nat.card S = p)
    (f : G → ℂ_[p]) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ g, ‖f g‖ ≤ B)
    (hf : ∀ g (h : S), f (g * h) = f g) : ‖∑ g, f g‖ ≤ B / p := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let : Fintype (G ⧸ S) := Fintype.ofFinite (G ⧸ S)
  rw [sum_eq_card_mul_quotient_sum S f hf, ← Nat.card_eq_fintype_card, hS, norm_mul]
  have hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    calc
      ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
        simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
      _ = (p : ℝ)⁻¹ := Padic.norm_p
  rw [hp, div_eq_mul_inv, mul_comm B]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB (fun q _ ↦ hb q.out)

/-- Invariance under translation by an element of order `p` improves a uniform bound by `1 / p`. -/
lemma order_p_invariant_sum_norm_le {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (k : G) (hk : orderOf k = p)
    (f : G → ℂ_[p]) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ g, ‖f g‖ ≤ B)
    (hf : ∀ g, f (g * k) = f g) : ‖∑ g, f g‖ ≤ B / p := by
  classical
  apply subgroup_invariant_sum_norm_le (Subgroup.zpowers k) ((Nat.card_zpowers k).trans hk)
    f hB hb
  intro g h
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr h.property)
  rw [← hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ, ← mul_assoc, hf] using ih

end HorizontalPadicL

end

-- FiniteFourier
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace HorizontalPadicL.FiniteFourier

variable {G K : Type*} [CommGroup G] [Fintype G] [Field K] [CharZero K]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] [Fintype (G →* Kˣ)]

omit [CharZero K] in
/-- Orthogonality of all characters of a finite abelian group. -/
lemma sum_characters [DecidableEq G] (x : G) :
    ∑ χ : G →* Kˣ, (χ x : K) = if x = 1 then (Fintype.card (G →* Kˣ) : K) else 0 := by
  classical
  split_ifs with hx
  · simp [hx]
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K hx
  have hχ' : (χ x : K) ≠ 1 := by simpa using hχ
  apply eq_zero_of_mul_eq_self_left hχ'
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft χ) _ _ fun ψ ↦ by simp

omit [CharZero K] in
/-- Finite Fourier inversion without dividing by the order of the dual group. -/
lemma inversion (f : G → K) (x : G) :
    ∑ χ : G →* Kˣ, (∑ y, f y * (χ y : K)) * (χ x⁻¹ : K) =
      f x * Fintype.card (G →* Kˣ) := by
  classical
  simp_rw [Finset.sum_mul, mul_assoc, ← Units.val_mul, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_characters]
  simp [mul_inv_eq_one]

/-- A function is determined by its character sums. -/
lemma injective (f g : G → K)
    (h : ∀ χ : G →* Kˣ, (∑ x, f x * (χ x : K)) = ∑ x, g x * (χ x : K)) : f = g := by
  funext x
  have hf := inversion f x
  have hg := inversion g x
  have hc : (Fintype.card (G →* Kˣ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_right_cancel₀ hc
  rw [← hf, ← hg]
  simp_rw [h]

/-- Fourier support on characters trivial on `k` implies translation invariance by `k`. -/
lemma invariant_of_vanish (f : G → K) (k : G)
    (h : ∀ χ : G →* Kˣ, χ k ≠ 1 → ∑ x, f x * (χ x : K) = 0) :
    ∀ x, f (k * x) = f x := by
  suffices (fun x ↦ f (k * x)) = f by exact fun x ↦ congrFun this x
  apply injective
  intro χ
  have hs : (∑ x, f (k * x) * (χ x : K)) =
      (χ k⁻¹ : K) * ∑ x, f x * (χ x : K) := by
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft k) _ _
    intro x
    simp [map_mul, mul_left_comm]
  rw [hs]
  by_cases hk : χ k = 1
  · simp [map_inv, hk]
  · rw [h χ hk, mul_zero]

omit [CharZero K] in
/-- Every character on the roots of unity is a power of the tautological character. -/
lemma roots_character_eq_pow {q : ℕ} [NeZero q] [HasEnoughRootsOfUnity K q]
    (χ : rootsOfUnity q K →* Kˣ) :
    ∃ a < q, ∀ h : rootsOfUnity q K, (χ h : K) = (h.val : K) ^ a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q
  let z : rootsOfUnity q K := hζ.toRootsOfUnity
  have hz : z ^ q = 1 := by
    apply Subtype.ext
    exact z.property
  have hχz : (χ z : K) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hz]
    simp
  obtain ⟨a, ha, hea⟩ := hζ.eq_pow_of_pow_eq_one hχz
  refine ⟨a, ha, fun h ↦ ?_⟩
  obtain ⟨b, hb, heb⟩ := hζ.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' q h.val).mp h.property)
  have heh : z ^ b = h := by
    apply rootsOfUnity.coe_injective
    simpa [z] using heb
  rw [← heh, map_pow, Units.val_pow_eq_pow_val, ← hea]
  simp [z, ← pow_mul, Nat.mul_comm]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] [Fintype (G →* Kˣ)] in
/-- Vanishing of the primitive cyclic frequencies implies invariance by all `p`-torsion. -/
lemma invariant_of_primitive_vanish [IsAlgClosed K] {p m : ℕ} [Fact p.Prime]
    [Fintype (rootsOfUnity (p ^ m) K)]
    (f : G × rootsOfUnity (p ^ m) K → K)
    (hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ η : G →* K, ∑ x, f x * η x.1 * (x.2.val : K) ^ a = 0)
    (k : rootsOfUnity (p ^ m) K) (hk : k ^ p = 1) :
    ∀ g h, f (g, h * k) = f (g, h) := by
  classical
  let : Fintype ((G × rootsOfUnity (p ^ m) K) →* Kˣ) := Fintype.ofFinite _
  have hinv : ∀ x : G × rootsOfUnity (p ^ m) K, f ((1, k) * x) = f x := by
    apply invariant_of_vanish
    intro χ hχ
    let χG : G →* Kˣ := χ.comp (MonoidHom.inl _ _)
    let χH : rootsOfUnity (p ^ m) K →* Kˣ := χ.comp (MonoidHom.inr _ _)
    obtain ⟨a, ha, hpow⟩ := roots_character_eq_pow χH
    have hap : Nat.Coprime a p := by
      apply Nat.Coprime.symm
      apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      rintro ⟨b, rfl⟩
      apply hχ
      apply Units.ext
      change (χH k : K) = 1
      rw [hpow, pow_mul]
      have hkp : (k.val : K) ^ p = 1 := by
        simpa using congrArg (fun z : rootsOfUnity (p ^ m) K ↦ (z.val : K)) hk
      rw [hkp, one_pow]
    have hh := hvanish a ha hap ((Units.coeHom K).comp χG)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x hx
    have hc : (χ x : K) = (χG x.1 : K) * (χH x.2 : K) := by
      change (χ x : K) = (χ (x.1, 1) : K) * (χ (1, x.2) : K)
      rw [← Units.val_mul, ← map_mul]
      simp
    rw [hc, hpow]
    simp [mul_assoc]
  intro g h
  simpa [mul_comm h k] using hinv (g, h)

/-- The finite Fourier estimate: primitive vanishing saves a factor of `p` in a marginal. -/
lemma marginal_norm_le_of_primitive_vanish {p m : ℕ} [Fact p.Prime]
    [Fintype (rootsOfUnity (p ^ m) ℂ_[p])]
    (hm : 0 < m) (f : G × rootsOfUnity (p ^ m) ℂ_[p] → ℂ_[p])
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ η : G →* ℂ_[p], ∑ x, f x * η x.1 * (x.2.val : ℂ_[p]) ^ a = 0) :
    ∀ g, ‖∑ h, f (g, h)‖ ≤ B / p := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
  have hpq : p ∣ p ^ m := dvd_pow_self _ hm.ne'
  let k : rootsOfUnity (p ^ m) ℂ_[p] :=
    ⟨hζ.toRootsOfUnity.val, rootsOfUnity_le_of_dvd hpq hζ.toRootsOfUnity.property⟩
  have hk : orderOf k = p := by
    rw [← Subgroup.orderOf_coe, ← orderOf_units]
    exact hζ.eq_orderOf.symm
  have hkp : k ^ p = 1 := by simpa only [hk] using pow_orderOf_eq_one k
  have hinv := invariant_of_primitive_vanish f hvanish k hkp
  intro g
  exact order_p_invariant_sum_norm_le k hk (fun h ↦ f (g, h)) hB
    (fun h ↦ hbound (g, h)) (hinv g)

end HorizontalPadicL.FiniteFourier

end

-- HorizontalTwists
set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Twisting after inflation agrees with the finite Fourier transform after truncation. -/
theorem HorizontalMeasure.eval_truncated_twist
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (m : ℕ) (he : ∀ n, m ≤ e n)
    (χ : HorizontalCharacter p e) (A : Finset ℕ)
    (ψ : HorizontalFiniteGroup p (fun _ ↦ m) χ.support →* rootsOfUnity (p ^ m) ℂ_[p])
    (hψ : (rootsOfUnityValue p (p ^ m)).comp
      (ψ.comp (truncateHorizontalCoordinatesHom m he χ.support)) = χ.toMonoidHom)
    (η : HorizontalFiniteGroup p (fun _ ↦ m) A →* ℂ_[p]) (a : ℕ) :
    μ.eval ((χ.powerOnSupport a).mulOnUnion (HorizontalCharacter.ofTruncated m he A η)) =
      (μ.truncatedFiniteLevel m he (A ∪ χ.support)).sum (fun y c ↦
        (c : ℂ_[p]) * ((rootsOfUnityValue p (p ^ m)
          (ψ (restrictHorizontalCoordinates Finset.subset_union_right y))) ^ a *
          η (restrictHorizontalCoordinates Finset.subset_union_left y))) := by
  have hs : ((χ.powerOnSupport a).mulOnUnion
      (HorizontalCharacter.ofTruncated m he A η)).support ⊆ A ∪ χ.support := by
    change χ.support ∪ A ⊆ A ∪ χ.support
    rw [Finset.union_comm]
  rw [μ.eval_eq_sum_of_support_subset _ hs, μ.truncatedFiniteLevel_eval]
  apply Finsupp.sum_congr
  intro x hx
  congr 1
  change χ.toMonoidHom (restrictHorizontalCoordinates Finset.subset_union_right x) ^ a *
    η (restrictHorizontalCoordinates Finset.subset_union_left
      (truncateHorizontalCoordinates m he (A ∪ χ.support) x)) = _
  have hval := DFunLike.congr_fun hψ
    (restrictHorizontalCoordinates Finset.subset_union_right x)
  change rootsOfUnityValue p (p ^ m)
    (ψ (truncateHorizontalCoordinates m he χ.support
      (restrictHorizontalCoordinates Finset.subset_union_right x))) = _ at hval
  rw [← hval]
  rfl

end HorizontalPadicL

end

-- MainFiniteCorrection
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open HorizontalPadicL

theorem solution
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (m : ℕ) (hm : 0 < m) (he : ∀ n, m ≤ e n)
    (A : Finset ℕ) (χ : HorizontalCharacter p e)
    (horder : orderOf χ.toMonoidHom = p ^ m) (_hdisjoint : Disjoint χ.support A)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : HorizontalFiniteGroup p (fun _ ↦ m) (A ∪ χ.support),
      ‖(μ.truncatedFiniteLevel m he (A ∪ χ.support) y : ℂ_[p])‖ ≤ B)
    (hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ ξ : HorizontalCharacter p e, ξ.support ⊆ A →
        orderOf ξ.toMonoidHom ∣ p ^ m →
        μ.eval ((χ.powerOnSupport a).mulOnUnion ξ) = 0) :
    ∀ x : HorizontalFiniteGroup p (fun _ ↦ m) A,
      ‖(μ.truncatedFiniteLevel m he A x : ℂ_[p])‖ ≤ B / (p : ℝ) := by
  classical
  let : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let : Fintype (rootsOfUnity (p ^ m) ℂ_[p]) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := χ.exists_truncated_roots m he
    (horder ▸ pow_orderOf_eq_one χ.toMonoidHom)
  let v := μ.truncatedFiniteLevel m he (A ∪ χ.support)
  let π : HorizontalFiniteGroup p (fun _ ↦ m) (A ∪ χ.support) →
      HorizontalFiniteGroup p (fun _ ↦ m) A × rootsOfUnity (p ^ m) ℂ_[p] :=
    fun y ↦ (restrictHorizontalCoordinates Finset.subset_union_left y,
      ψ (restrictHorizontalCoordinates Finset.subset_union_right y))
  let l := Finsupp.mapDomain π v
  have hlbound : ∀ z, ‖(l z : ℂ_[p])‖ ≤ B :=
    norm_mapDomain_apply_le v π B hB hbound
  have hlvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ η : HorizontalFiniteGroup p (fun _ ↦ m) A →* ℂ_[p],
        ∑ z, (l z : ℂ_[p]) * η z.1 * (z.2.val : ℂ_[p]) ^ a = 0 := by
    intro a ha hap η
    have hv := hvanish a ha hap (HorizontalCharacter.ofTruncated m he A η)
      (Finset.Subset.refl A) (HorizontalCharacter.ofTruncated_order_dvd m he A η)
    rw [μ.eval_truncated_twist m he χ A ψ hψ η a] at hv
    calc
      _ = ∑ z, (l z : ℂ_[p]) * (η z.1 * (z.2.val : ℂ_[p]) ^ a) := by
        simp only [mul_assoc]
      _ = v.sum (fun y c ↦ (c : ℂ_[p]) *
          (η (π y).1 * ((π y).2.val : ℂ_[p]) ^ a)) :=
        mapDomain_sum_mul v π _
      _ = 0 := by
        convert hv using 1
        apply Finsupp.sum_congr
        intro y hy
        exact congrArg (fun z : ℂ_[p] ↦ (v y : ℂ_[p]) * z) (mul_comm _ _)
  have hproj : Finsupp.mapDomain Prod.fst l = μ.truncatedFiniteLevel m he A := by
    change Finsupp.mapDomain Prod.fst (Finsupp.mapDomain π v) = _
    rw [← Finsupp.mapDomain_comp]
    exact μ.truncatedFiniteLevel_compatible m he Finset.subset_union_left
  have hnorm := FiniteFourier.marginal_norm_le_of_primitive_vanish hm
    (fun z ↦ (l z : ℂ_[p])) hB hlbound hlvanish
  intro x
  have hsum : (∑ h, (l (x, h) : ℂ_[p])) = (μ.truncatedFiniteLevel m he A x : ℂ_[p]) := by
    change (∑ h, R.subtype (l (x, h))) = _
    rw [← map_sum, ← mapDomain_fst_apply, hproj]
    rfl
  simpa only [hsum] using hnorm x

end
