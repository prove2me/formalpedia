-- Prove2me | solution 1 for ModularCurve.card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/45f4b6ef-fbc5-53ed-aca4-c889732762c8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer

set_option autoImplicit false

open MulAction
open scoped MatrixGroups

namespace Ws49
namespace OrbitStab

section General

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem card_stabilizer_subgroup (L : Subgroup G) (a : α) :
    Nat.card (stabilizer L a) = Nat.card (L ⊓ stabilizer G a : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, by
        have h := g.2
        rw [mem_stabilizer_iff, Subgroup.smul_def] at h
        exact h⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, by
        rw [mem_stabilizer_iff, Subgroup.smul_def]
        exact g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem relIndex_stabilizer_smul_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) (x : α) :
    H.relIndex (stabilizer G (g • x)) = H.relIndex (stabilizer G x) := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hH]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem relIndex_stabilizer_mul_card_stabilizer (H : Subgroup G) (x : α) :
    H.relIndex (stabilizer G x) * Nat.card (stabilizer H x) = Nat.card (stabilizer G x) := by
  rw [card_stabilizer_subgroup, ← Subgroup.subgroupOf_map_subtype,
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv.symm,
    Subgroup.relIndex, mul_comm]
  exact Subgroup.card_mul_index _

variable (H : Subgroup G) (a : α)

private def fib : Quotient (QuotientGroup.rightRel H) → orbitRel.Quotient H (orbit G a) :=
  Quotient.lift (fun g : G => Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩) (by
    intro g g' hgg'
    have hgg'' : g' * g⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hgg'
    refine Quotient.sound (mem_orbit_iff.mpr ?_)
    refine ⟨⟨g * g'⁻¹, by simpa using H.inv_mem hgg''⟩, Subtype.ext ?_⟩
    show (g * g'⁻¹) • g' • a = g • a
    rw [smul_smul, inv_mul_cancel_right])

private theorem fib_mk (g : G) :
    fib H a (Quotient.mk _ g) = Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩ := rfl

private theorem fib_surjective : Function.Surjective (fib H a) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp x.2
    exact ⟨Quotient.mk _ g, by rw [fib_mk]; congr 1; exact Subtype.ext hg⟩

theorem finite_orbitRelQuotient_orbit [H.FiniteIndex] : Finite (orbitRel.Quotient H (orbit G a)) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Finite.of_surjective _ (fib_surjective H a)

private theorem card_fiber (q : orbitRel.Quotient H (orbit G a)) :
    Nat.card {c // fib H a c = q} = H.relIndex (stabilizer G ((q.out : orbit G a) : α)) := by
  classical
  set x : orbit G a := q.out with hx
  obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp x.2
  have hq : Quotient.mk (orbitRel H (orbit G a)) x = q := Quotient.out_eq q
  let K : Subgroup G := stabilizer G (x : α)

  let φ : K → {c // fib H a c = q} := fun k => ⟨Quotient.mk _ ((k : G) * g₀), by
    rw [fib_mk, ← hq]
    congr 1
    apply Subtype.ext
    show ((k : G) * g₀) • a = (x : α)
    rw [mul_smul, hg₀]
    exact k.2⟩
  have hφ : ∀ k k' : K, φ k = φ k' ↔ QuotientGroup.rightRel (H.subgroupOf K) k k' := by
    intro k k'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    show Quotient.mk (QuotientGroup.rightRel H) ((k : G) * g₀) = Quotient.mk _ ((k' : G) * g₀) ↔ _
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
    simp [mul_assoc]
  let ψ : Quotient (QuotientGroup.rightRel (H.subgroupOf K)) → {c // fib H a c = q} :=
    Quotient.lift φ (fun k k' h => (hφ k k').mpr h)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro c c'
      induction c using Quotient.inductionOn with
      | h k =>
        induction c' using Quotient.inductionOn with
        | h k' =>
          intro h
          exact Quotient.sound ((hφ k k').mp h)
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with
      | h g =>
        rw [fib_mk, ← hq] at hc
        have hc' : (⟨g • a, mem_orbit a g⟩ : orbit G a) ∈ orbit H x := Quotient.exact hc
        obtain ⟨h, hh⟩ := mem_orbit_iff.mp hc'
        have hh' : (h : G) • (x : α) = g • a := congrArg Subtype.val hh
        refine ⟨Quotient.mk _ ⟨(h : G)⁻¹ * g * g₀⁻¹, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg₀, inv_smul_smul, hg₀, ← hh', inv_smul_smul]
        · apply Subtype.ext
          show Quotient.mk (QuotientGroup.rightRel H) (((h : G)⁻¹ * g * g₀⁻¹) * g₀) = Quotient.mk _ g
          refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
          simp [mul_assoc]
  rw [← Nat.card_eq_of_bijective ψ hψ, Subgroup.relIndex, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf K))]

theorem exists_smul_out_eq (b : orbit G a) :
    ∃ h ∈ H, h • (((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) : α) = b := by
  have hrel : ((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) ∈ orbit H b :=
    Quotient.mk_out (s := orbitRel H (orbit G a)) b
  obtain ⟨h, hh⟩ := mem_orbit_iff.mp hrel
  refine ⟨((h⁻¹ : H) : G), (h⁻¹).2, ?_⟩
  rw [← hh, Subgroup.coe_inv]
  show (h : G)⁻¹ • (h : G) • (b : α) = b
  rw [inv_smul_smul]

theorem finsum_relIndex_stabilizer_eq_index [H.FiniteIndex] :
    ∑ᶠ q : orbitRel.Quotient H (orbit G a),
        H.relIndex (stabilizer G ((q.out : orbit G a) : α)) = H.index := by
  classical
  haveI := finite_orbitRelQuotient_orbit H a
  haveI : Fintype (orbitRel.Quotient H (orbit G a)) := Fintype.ofFinite _
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  rw [finsum_eq_sum_of_fintype, Subgroup.index,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (fib H a)), Nat.card_sigma]
  exact Finset.sum_congr rfl fun q _ => (card_fiber H a q).symm

end General

section PlusMinus

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem mem_or_mul_mem_of_mem_sup_zpowers (H : Subgroup G) {z : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) {g : G} (hg : g ∈ H ⊔ Subgroup.zpowers z) : g ∈ H ∨ g * z ∈ H := by
  have hcomm : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  let K : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * z ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y, ← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (x * z) * (y * z) := by
            rw [mul_assoc, ← mul_assoc z, ← hcomm y, mul_assoc y, hz2, mul_one]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          have : x⁻¹ * z = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv, hcomm]
          rw [this]
          exact H.inv_mem hx }
  have hle : H ⊔ Subgroup.zpowers z ≤ K := by
    refine sup_le (fun g hg => Or.inl hg) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hz2]; exact H.one_mem)
  exact hle hg

theorem card_stabilizer_sup_zpowers_mul_card_inf (H : Subgroup G) {z : G}
    (hz : z ∈ Subgroup.center G) (hz2 : z * z = 1) (hz1 : z ≠ 1) (a : α) (hza : z • a = a) :
    Nat.card (stabilizer (H ⊔ Subgroup.zpowers z : Subgroup G) a) *
        Nat.card (H ⊓ Subgroup.zpowers z : Subgroup G) =
      2 * Nat.card (stabilizer H a) := by
  classical
  set Z : Subgroup G := Subgroup.zpowers z with hZ
  set S : Subgroup G := stabilizer G a with hS
  have hcardZ : Nat.card Z = 2 := by
    rw [hZ, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two, hz2]) hz1
  have hzS : z ∈ S := hza
  rw [card_stabilizer_subgroup, card_stabilizer_subgroup]
  by_cases hzH : z ∈ H
  ·
    have hZH : Z ≤ H := by rw [hZ, Subgroup.zpowers_le]; exact hzH
    rw [sup_eq_left.mpr hZH, inf_eq_right.mpr hZH, hcardZ, mul_comm]
  ·
    have hinf : Nat.card (H ⊓ Z : Subgroup G) = 1 := by
      have hdvd : Nat.card (H ⊓ Z : Subgroup G) ∣ 2 := hcardZ ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · exfalso
        apply hzH
        haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcardZ]; decide)
        have heq : H ⊓ Z = Z :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardZ])
        have : z ∈ H ⊓ Z := by rw [heq, hZ]; exact Subgroup.mem_zpowers z
        exact this.1
    rw [hinf, mul_one]
    set A : Subgroup G := (H ⊔ Z) ⊓ S with hA
    set B : Subgroup G := H ⊓ S with hB
    have hBA : B ≤ A := inf_le_inf_right S le_sup_left
    have hidx : (B.subgroupOf A).index = 2 := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_eq_two_iff]
      refine ⟨z, ⟨Subgroup.mem_sup_right (by rw [hZ]; exact Subgroup.mem_zpowers z), hzS⟩, ?_⟩
      rintro b ⟨hbHZ, hbS⟩
      have hbzS : b * z ∈ S := S.mul_mem hbS hzS
      rcases mem_or_mul_mem_of_mem_sup_zpowers H hz hz2 hbHZ with hbH | hbzH
      ·
        refine Or.inr ⟨⟨hbH, hbS⟩, ?_⟩
        rintro ⟨hbz, -⟩
        exact hzH (by simpa using H.mul_mem (H.inv_mem hbH) hbz)
      · refine Or.inl ⟨⟨hbzH, hbzS⟩, ?_⟩
        rintro ⟨hbH, -⟩
        exact hzH (by simpa using H.mul_mem (H.inv_mem hbH) hbzH)
    have hcard : Nat.card A = Nat.card B * 2 := by
      rw [← hidx, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
      exact (Subgroup.card_mul_index _).symm
    rw [hcard, mul_comm]

theorem negOne_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem negOne_mul_negOne : (-1 : SL(2, ℤ)) * (-1) = 1 := by
  rw [neg_one_mul, neg_neg]

theorem negOne_ne_one : (-1 : SL(2, ℤ)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at h00

theorem negOne_smul (τ : UpperHalfPlane) : (-1 : SL(2, ℤ)) • τ = τ := by
  rw [ModularGroup.SL_neg_smul, one_smul]

theorem card_stabilizer_negOne_sup_mul_card_inf_zpowers_negOne (Γ : Subgroup SL(2, ℤ))
    (τ : UpperHalfPlane) :
    Nat.card (stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) *
        Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) =
      2 * Nat.card (stabilizer Γ τ) :=
  card_stabilizer_sup_zpowers_mul_card_inf Γ negOne_mem_center negOne_mul_negOne negOne_ne_one τ
    (negOne_smul τ)

theorem finsum_relIndex_stabilizer_eq_index_negOne_sup (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (τ : UpperHalfPlane) :
    ∑ᶠ q : orbitRel.Quotient (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))
        (orbit SL(2, ℤ) τ),
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).relIndex
          (stabilizer SL(2, ℤ) ((q.out : orbit SL(2, ℤ) τ) : UpperHalfPlane))
      = (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  haveI : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  exact finsum_relIndex_stabilizer_eq_index _ τ

end PlusMinus

end Ws49.OrbitStab

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) *
        Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) =
      2 * Nat.card (MulAction.stabilizer Γ τ) :=
  Ws49.OrbitStab.card_stabilizer_negOne_sup_mul_card_inf_zpowers_negOne Γ τ

end S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer
end P2MW
export P2MW.S_ModularCurve_card_stabilizer_sup_zpowers_negOne_mul_card_inf_eq_two_mul_card_stabilizer (solution)
