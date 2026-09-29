-- Prove2me | solution 1 for NumberField.exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fbde8b77-960a-5b9c-8f33-cd5743d54372

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain Topology

noncomputable section

namespace Ws31
namespace FinUnit

variable (K : Type) [Field K] [NumberField K]

def O (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {u | (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K}
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem ha.1 hb.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem hb.2 ha.2
  one_mem' := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem mem_O {v : HeightOneSpectrum (𝓞 K)} {u : (v.adicCompletion K)ˣ} :
    u ∈ O K v ↔ (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := Iff.rfl

theorem valued_le_one_of_mem_O {v : HeightOneSpectrum (𝓞 K)} {u : (v.adicCompletion K)ˣ} (hu : u ∈ O K v) :
    Valued.v (u : v.adicCompletion K) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hu.1

variable (N : Ideal (𝓞 K))

def U (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {u | u ∈ O K v ∧ Valued.v ((u : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v}
  mul_mem' := by
    intro a b ha hb
    refine ⟨(O K v).mul_mem ha.1 hb.1, ?_⟩
    have h : ((a * b : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (a : v.adicCompletion K) * ((b : v.adicCompletion K) - 1) + ((a : v.adicCompletion K) - 1) := by
      rw [Units.val_mul]; ring
    rw [h]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ha.2)
    rw [map_mul]
    exact mul_le_of_le_one_of_le (valued_le_one_of_mem_O K ha.1) hb.2
  one_mem' := ⟨(O K v).one_mem, by simp⟩
  inv_mem' := by
    intro a ha
    refine ⟨(O K v).inv_mem ha.1, ?_⟩
    have h : (((a⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) - 1 =
        -((((a⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) * ((a : v.adicCompletion K) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]; ring
    rw [h, Valuation.map_neg, map_mul]
    exact mul_le_of_le_one_of_le (valued_le_one_of_mem_O K ((O K v).inv_mem ha.1)) ha.2

theorem mem_U {v : HeightOneSpectrum (𝓞 K)} {u : (v.adicCompletion K)ˣ} :
    u ∈ U K N v ↔ u ∈ O K v ∧ Valued.v ((u : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v := Iff.rfl

theorem U_le_O (v : HeightOneSpectrum (𝓞 K)) : U K N v ≤ O K v := fun _ h => h.1

def U' (v : HeightOneSpectrum (𝓞 K)) : Subgroup (O K v) := (U K N v).subgroupOf (O K v)

theorem isCompact_O (v : HeightOneSpectrum (𝓞 K)) : IsCompact ((O K v : Set (v.adicCompletion K)ˣ)) := by
  let f : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ := Units.map (v.adicCompletionIntegers K).subtype
  have hf : Continuous f := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact continuous_subtype_val.comp Units.continuous_val
    · exact continuous_subtype_val.comp Units.continuous_coe_inv
  have hrange : Set.range f = (O K v : Set (v.adicCompletion K)ˣ) := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(w : v.adicCompletionIntegers K).2, by rw [← map_inv]; exact ((w⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2⟩
    · intro hu
      refine ⟨⟨⟨(u : v.adicCompletion K), hu.1⟩, ⟨((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), hu.2⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩
  rw [← hrange]
  exact isCompact_range hf

scoped instance compactSpace_O (v : HeightOneSpectrum (𝓞 K)) : CompactSpace (O K v) :=
  isCompact_iff_compactSpace.mp (isCompact_O K v)

theorem isOpen_U' (v : HeightOneSpectrum (𝓞 K)) (hN : N ≠ ⊥) : IsOpen ((U' K N v : Set (O K v))) := by
  have h1 : (U' K N v : Set (O K v)) =
      (fun x : O K v => (((x : (v.adicCompletion K)ˣ)) : v.adicCompletion K) - 1) ⁻¹'
        {y : v.adicCompletion K | Valued.v y ≤ idealBound (𝓞 K) N v} := by
    ext x
    simp only [U', Subgroup.coe_subgroupOf, Set.mem_preimage, SetLike.mem_coe, mem_U, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [h1]
  exact (isOpen_setOf_valued_le_idealBound (K := K) v hN).preimage
    ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const)

scoped instance finite_quot (v : HeightOneSpectrum (𝓞 K)) [hN : Fact (N ≠ ⊥)] : Finite (O K v ⧸ U' K N v) :=
  Subgroup.quotient_finite_of_isOpen _ (isOpen_U' K N v hN.out)

end Ws31.FinUnit
p2m_reactivate "P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31 P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31.FinUnit"
p2m_reactivate "P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31"

namespace Ws31
namespace FinUnit

variable (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K))

def idx (v : HeightOneSpectrum (𝓞 K)) : ℕ := Nat.card (O K v ⧸ U' K N v)

theorem idx_pos (v : HeightOneSpectrum (𝓞 K)) [Fact (N ≠ ⊥)] : 0 < idx K N v :=
  Nat.card_pos

def Triv (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  ∀ t : (v.adicCompletion K)ˣ, (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
    ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
    Valued.v ((t : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v → χ t = 1

theorem ker_cond (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Triv K N v χ) :
    ∀ x ∈ U' K N v, (χ.comp (O K v).subtype) x = 1 := by
  intro x hx
  have hx' : (x : (v.adicCompletion K)ˣ) ∈ U K N v := hx
  exact hχ _ hx'.1.1 hx'.1.2 hx'.2

def ψ (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Triv K N v χ) :
    O K v ⧸ U' K N v →* ℂˣ :=
  QuotientGroup.lift (U' K N v) (χ.comp (O K v).subtype) (ker_cond K N v χ hχ)

theorem ψ_mk (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Triv K N v χ) (x : O K v) :
    ψ K N v χ hχ (QuotientGroup.mk x) = χ (x : (v.adicCompletion K)ˣ) :=
  QuotientGroup.lift_mk _ _ _

def T (v : HeightOneSpectrum (𝓞 K)) [Fact (N ≠ ⊥)] (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Triv K N v χ) :
    (O K v ⧸ U' K N v) → rootsOfUnity (idx K N v) ℂ := fun q =>
  ⟨ψ K N v χ hχ q, by
    rw [mem_rootsOfUnity, ← map_pow, idx, pow_card_eq_one', map_one]⟩

theorem eq_of_T_eq (v : HeightOneSpectrum (𝓞 K)) [Fact (N ≠ ⊥)] (χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h₁ : Triv K N v χ₁) (h₂ : Triv K N v χ₂) (h : T K N v χ₁ h₁ = T K N v χ₂ h₂)
    (u : (v.adicCompletion K)ˣ) (hu : u ∈ O K v) : χ₁ u = χ₂ u := by
  have := congrArg (fun f => ((f (QuotientGroup.mk ⟨u, hu⟩) : rootsOfUnity (idx K N v) ℂ) : ℂˣ)) h
  simp only [T] at this
  rwa [ψ_mk, ψ_mk] at this

theorem main (SK : Finset (HeightOneSpectrum (𝓞 K))) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (ρs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
    ∀ (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (_hχ : ∀ v ∈ SK, ∀ t : (v.adicCompletion K)ˣ, (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        Valued.v ((t : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v → χ v t = 1),
    ∃ r : Fin n, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        χ v u = ρs r v u := by
  classical
  haveI : Fact (N ≠ ⊥) := ⟨hN⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), NeZero (idx K N v) := fun v => ⟨(idx_pos K N v).ne'⟩
  let I : Type := (w : SK) → ((O K w.1 ⧸ U' K N w.1) → rootsOfUnity (idx K N w.1) ℂ)
  haveI : Finite I := inferInstance
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let ρs : Fin m → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ := fun r v =>
    if hv : v ∈ SK then
      (if h : ∃ χ' : (v.adicCompletion K)ˣ →* ℂˣ, ∃ hχ' : Triv K N v χ', T K N v χ' hχ' = (e.symm r) ⟨v, hv⟩
        then h.choose else 1)
    else 1
  refine ⟨m, ρs, fun χ hχ => ?_⟩
  let I₀ : I := fun w => T K N w.1 (χ w.1) (hχ w.1 w.2)
  refine ⟨e I₀, fun v hv u hu hu' => ?_⟩
  have hex : ∃ χ' : (v.adicCompletion K)ˣ →* ℂˣ, ∃ hχ' : Triv K N v χ', T K N v χ' hχ' = (e.symm (e I₀)) ⟨v, hv⟩ :=
    ⟨χ v, hχ v hv, by rw [Equiv.symm_apply_apply]⟩
  have hρ : ρs (e I₀) v = hex.choose := by
    simp only [ρs, dif_pos hv, dif_pos hex]
  obtain ⟨hχ', hT⟩ := hex.choose_spec
  have hT' : T K N v hex.choose hχ' = I₀ ⟨v, hv⟩ := hT.trans (congrFun (e.symm_apply_apply I₀) ⟨v, hv⟩)
  rw [hρ]
  exact (eq_of_T_eq K N v _ _ hχ' (hχ v hv) hT' u ⟨hu, hu'⟩).symm

end Ws31.FinUnit
p2m_reactivate "P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31 P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31.FinUnit"
p2m_reactivate "P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31 P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31.FinUnit"

end
p2m_reactivate "P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31 P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.Ws31.FinUnit"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (ρs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
    ∀ (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (_hχ : ∀ v ∈ SK, ∀ t : (v.adicCompletion K)ˣ, (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        Valued.v ((t : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v → χ v t = 1),
    ∃ r : Fin n, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        χ v u = ρs r v u :=
  Ws31.FinUnit.main K N SK hN

end S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
end P2MW
export P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits (solution)
