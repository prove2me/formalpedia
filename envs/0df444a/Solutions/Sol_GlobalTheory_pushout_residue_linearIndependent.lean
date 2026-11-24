-- Prove2me | solution 1 for GlobalTheory.pushout_residue_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:15.06456+00:00
-- url     : https://prove2.me/submissions/25500a05-baab-4102-81ef-0817fd95c964

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PushoutResidueLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTD n x hx d hd j

  haveI : IsLocalHom (algebraMap T D) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal T := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap T D a ∈ maximalIdeal D := hTD ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha
  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _

  let v : Fin n → A ⧸ (maximalIdeal T • (⊤ : Submodule T A)) := fun i => Submodule.Quotient.mk (x i)
  have hmem : ∀ y : A, y ∈ maximalIdeal T • (⊤ : Submodule T A) ↔
      y ∈ (maximalIdeal T).map (algebraMap T A) := by
    intro y; rw [Ideal.smul_top_eq_map]; rfl
  have hli : LinearIndependent (T ⧸ maximalIdeal T) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨c', rfl⟩ : ∃ c' : Fin n → T, (fun k => Ideal.Quotient.mk (maximalIdeal T) (c' k)) = c :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (c k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (c k)).choose_spec⟩
    have hsum : (∑ k, Ideal.Quotient.mk (maximalIdeal T) (c' k) • v k) =
        Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (∑ k, c' k • x k) := by
      rw [← Submodule.mkQ_apply, map_sum]
      rfl
    rw [hsum, Submodule.Quotient.mk_eq_zero, hmem] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hx c' hc i)

  let bs := Module.Basis.span hli
  obtain ⟨f, hf⟩ := LinearMap.exists_extend (K := T ⧸ maximalIdeal T) (bs.coord j)
  have hfv : ∀ i, f (v i) = if i = j then 1 else 0 := by
    intro i
    have := congrArg (fun F => F (bs i)) hf
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Module.Basis.coord_apply,
      Module.Basis.repr_self] at this
    rw [Module.Basis.span_apply] at this
    rw [this, Finsupp.single_apply]

  let φ : T ⧸ maximalIdeal T →+* ResidueField D := ResidueField.map (algebraMap T D)
  have hφ : ∀ t : T, φ (Ideal.Quotient.mk _ t) = algebraMap T (ResidueField D) t := fun t => rfl

  let g : A →ₗ[T] ResidueField D :=
    { toFun := fun a => φ (f (Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a))
      map_add' := fun a b => by simp only [Submodule.Quotient.mk_add, map_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply]
        have hq : Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (t • a) =
            Ideal.Quotient.mk (maximalIdeal T) t •
              Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a :=
          (Module.Quotient.mk_smul_mk A (maximalIdeal T) t a).symm
        rw [hq, map_smul, smul_eq_mul, map_mul, hφ, ← Algebra.smul_def] }
  have hg : ∀ i, g (x i) = if i = j then 1 else 0 := by
    intro i
    show φ (f (v i)) = _
    rw [hfv]; split_ifs <;> simp

  have hbc := (Algebra.IsPushout.out (R := T) (S := D) (R' := A) (S' := B))
  let ψ := hbc.lift g
  have hψ : ∀ a : A, ψ (algebraMap A B a) = g a := fun a => hbc.lift_eq g a
  have hkill : ∀ y ∈ (maximalIdeal D).map (algebraMap D B), ψ y = 0 := by
    intro y hy
    have hy' : y ∈ maximalIdeal D • (⊤ : Submodule D B) := by
      rw [Ideal.smul_top_eq_map]; exact hy
    refine Submodule.smul_induction_on hy' ?_ ?_
    · intro r hr b _
      rw [map_smul, Algebra.smul_def]
      have : algebraMap D (ResidueField D) r = 0 := (residue_eq_zero_iff r).2 hr
      rw [this, zero_mul]
    · intro a b ha hb; rw [map_add, ha, hb, add_zero]
  have := hkill _ hd
  rw [map_sum, Finset.sum_eq_single j (fun i _ hi => by rw [map_smul, hψ, hg, if_neg hi, smul_zero])
    (by simp)] at this
  rw [map_smul, hψ, hg, if_pos rfl, Algebra.smul_def, mul_one] at this
  exact (residue_eq_zero_iff _).1 this
end GlobalTheory
