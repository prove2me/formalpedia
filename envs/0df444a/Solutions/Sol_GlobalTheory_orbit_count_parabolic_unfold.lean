-- Prove2me | solution 1 for GlobalTheory.orbit_count_parabolic_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:19.17986+00:00
-- url     : https://prove2.me/submissions/3dbb852b-6331-4ddc-b683-dc875a5eb2ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitCountParabolicUnfoldLevi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK huK TM CM TP CP _ hTP _ _ q X
  set S : Subgroup M := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM with hS
  set C : Subgroup M := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s) with hC
  letI : MulAction M (P ⧸ KP) := MulAction.compHom (P ⧸ KP) s
  have hsmul : ∀ (r : M) (p : P), r • (QuotientGroup.mk p : P ⧸ KP) = QuotientGroup.mk (s r * p) := by
    intro r p; rfl
  have memS : ∀ r : M, r ∈ S ↔ (∃ t ∈ TM, q⁻¹ * t * q = r) ∧ r ∈ KM := by
    intro r
    simp only [hS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  set x0 : P ⧸ KP := QuotientGroup.mk (u X) with hx0
  have key : ∀ Y : N, DoubleCoset.mk TP KP (s q * u Y) = DoubleCoset.mk TP KP (s q * u X) ↔
      (QuotientGroup.mk (u Y) : P ⧸ KP) ∈ MulAction.orbit S x0 := by
    intro Y
    rw [eq_comm, DoubleCoset.eq]
    constructor
    · rintro ⟨h, hh, k, hk, e⟩
      obtain ⟨t, ht, rfl⟩ := (hTP h).1 hh
      have e2 : u Y = s (q⁻¹ * t * q) * u X * k := by
        apply mul_left_cancel (a := s q)
        rw [e, map_mul, map_mul, map_inv]
        group
      have e3 := congrArg π e2
      simp only [map_mul, hπs, hπu, mul_one] at e3
      have e4 : q⁻¹ * t * q = (π k)⁻¹ := eq_inv_of_mul_eq_one_left e3.symm
      have hr : q⁻¹ * t * q ∈ S := (memS _).2 ⟨⟨t, ht, rfl⟩, e4 ▸ KM.inv_mem (hπK k hk)⟩
      refine ⟨⟨_, hr⟩, ?_⟩
      show (q⁻¹ * t * q) • x0 = _
      rw [hx0, hsmul, QuotientGroup.eq, e2]
      convert hk using 1
      group
    · rintro ⟨⟨r, hr⟩, e⟩
      change r • x0 = _ at e
      rw [hx0, hsmul, QuotientGroup.eq] at e
      obtain ⟨⟨t, ht, rfl⟩, -⟩ := (memS r).1 hr
      refine ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, _, e, ?_⟩
      simp only [map_mul, map_inv]
      group
  have hinj : ∀ x y : N ⧸ L, (QuotientGroup.mk (u (Quotient.out x)) : P ⧸ KP) = QuotientGroup.mk (u (Quotient.out y)) → x = y := by
    intro x y h
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, huK] at h
    rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
    exact (QuotientGroup.eq (s := L)).2 h
  have hcard : Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = Nat.card (MulAction.orbit S x0) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨QuotientGroup.mk (u (Quotient.out x.1)), (key _).1 x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨y, ⟨⟨r, hr⟩, rfl⟩⟩
      have hk : π (s r * u X * (s r)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hπs, hπu]; group
      obtain ⟨Z, hZ⟩ := (hker _).1 hk
      have hrK : (r : M) ∈ KM := ((memS r).1 hr).2
      have hyo : (QuotientGroup.mk (u (Quotient.out (QuotientGroup.mk Z : N ⧸ L))) : P ⧸ KP) = r • x0 := by
        obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L Z
        change _ = r • x0
        rw [hx0, hsmul, hl, QuotientGroup.eq, map_mul, hZ]
        have h1 : s (r : M) ∈ KP := hsK _ hrK
        have h2 : u (l : N) ∈ KP := (huK _).2 l.2
        convert KP.mul_mem (KP.inv_mem h2) h1 using 1
        group
      refine ⟨⟨QuotientGroup.mk Z, (key _).2 ?_⟩, ?_⟩
      · rw [hyo]; exact ⟨⟨r, hr⟩, rfl⟩
      · exact Subtype.ext hyo
  have hstab : MulAction.stabilizer S x0 = (S ⊓ C).subgroupOf S := by
    ext ⟨r, hr⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC, Subgroup.mem_comap]
    change (r • x0 = x0) ↔ _
    rw [hx0, hsmul, QuotientGroup.eq]
    simp only [hr, true_and, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply, inv_inv]
    rw [← KP.inv_mem_iff]
    constructor <;> intro h <;> convert h using 1 <;> group
  rw [hcard, Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
end GlobalTheory
