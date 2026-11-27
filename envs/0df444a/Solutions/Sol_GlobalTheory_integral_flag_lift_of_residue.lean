-- Prove2me | solution 1 for GlobalTheory.integral_flag_lift_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:05.707487+00:00
-- url     : https://prove2.me/submissions/37fc39db-99e8-42a8-b8b0-e1e540b10bf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFlagLiftOfResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (O Γ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O), Irreducible ϖ → a + t = n → (∀ g m, ((r g : Matrix (Fin n) (Fin n) O).charpoly - (ρ g : Matrix (Fin a) (Fin a) O).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : Oˣ) : O))).coeff m ∈ IsLocalRing.maximalIdeal O) → (∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc) → ∃ (R : ℕ) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun i => ϖ * y i) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧ (∀ g j x, x ∈ M j → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun i => ((ψ s g : Oˣ) : O) * x i) ∈ M (rs s).castSucc := by
  intro O Γ _ _ _ _ n a t r ρ ψ ϖ hϖ hat hcong hfield
  let k := IsLocalRing.ResidueField O
  let f : O →+* k := IsLocalRing.residue O
  let rk : Γ →* GL (Fin n) k := (Matrix.GeneralLinearGroup.map f).comp r
  let ρk : Γ →* GL (Fin a) k := (Matrix.GeneralLinearGroup.map f).comp ρ
  let ψk : Fin t → Γ →* kˣ := fun s => (Units.map f.toMonoidHom).comp (ψ s)
  have hrk : ∀ g, (rk g : Matrix (Fin n) (Fin n) k) = (r g : Matrix (Fin n) (Fin n) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (r g)
  have hρk : ∀ g, (ρk g : Matrix (Fin a) (Fin a) k) = (ρ g : Matrix (Fin a) (Fin a) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (ρ g)
  have hψk : ∀ s g, ((ψk s g : kˣ) : k) = f ((ψ s g : Oˣ) : O) := fun s g => rfl
  have hchar : ∀ g, (rk g : Matrix (Fin n) (Fin n) k).charpoly
      = (ρk g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (X - C ((ψk s g : kˣ) : k)) := by
    intro g
    rw [hrk, hρk, Matrix.charpoly_map, Matrix.charpoly_map]
    simp_rw [hψk]
    have hp : ∏ s, (X - C (f ((ψ s g : Oˣ) : O)))
        = (∏ s, (X - C ((ψ s g : Oˣ) : O))).map f := by
      simp [Polynomial.map_prod]
    rw [hp, ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    ext m
    rw [coeff_map, coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hcong g m)
  obtain ⟨R, V, rs, hV0, hVtop, hVmono, hVstab, hrs, hstep⟩ :=
    hfield k Γ n a t rk ρk ψk hat hchar
  let π : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  have hπ : ∀ x i, π x i = f (x i) := fun x i => rfl
  have hπsurj : ∀ y : Fin n → k, ∃ x, π x = y := by
    intro y
    choose x hx using fun i => IsLocalRing.residue_surjective (y i)
    exact ⟨x, funext hx⟩
  have hπmul : ∀ g x, π ((r g : Matrix (Fin n) (Fin n) O).mulVec x)
      = (rk g : Matrix (Fin n) (Fin n) k).mulVec (π x) := by
    intro g x; funext i; rw [hπ, RingHom.map_mulVec, hrk]; rfl
  let M : Fin (R + 1) → Submodule O (Fin n → O) := fun j => ((V j).restrictScalars O).comap π
  have hM : ∀ j x, x ∈ M j ↔ π x ∈ V j := fun j x => Iff.rfl
  have hMmono : Monotone M := fun i j hij x hx => hVmono hij hx
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  refine ⟨R, M, rs, ?_, ?_, hMmono, ?_, hrs, ?_⟩
  · intro x
    rw [hM, hV0, Submodule.mem_bot]
    constructor
    · intro hx
      have : ∀ i, ∃ y, x i = ϖ * y := by
        intro i
        have h1 : x i ∈ IsLocalRing.maximalIdeal O := by
          rw [← IsLocalRing.residue_eq_zero_iff]; exact congr_fun hx i
        rw [hmax, Ideal.mem_span_singleton] at h1
        obtain ⟨y, hy⟩ := h1
        exact ⟨y, hy⟩
      choose y hy using this
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      show f (ϖ * y i) = 0
      rw [map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ), zero_mul]
  · ext x
    simp only [hM, hVtop, Submodule.mem_top]
  · intro g j x hx
    rw [hM, hπmul]
    exact hVstab g j _ hx
  · intro s
    obtain ⟨xb, hxb, hxbn, hsup, hchi⟩ := hstep s
    obtain ⟨x, rfl⟩ := hπsurj xb
    refine ⟨x, hxb, hxbn, ?_, ?_⟩
    · apply le_antisymm
      · intro y hy
        rw [hM, hsup, Submodule.mem_sup] at hy
        obtain ⟨v, hv, w, hw, hvw⟩ := hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
        rw [Submodule.mem_sup]
        refine ⟨y - c' • x, ?_, c' • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x),
          sub_add_cancel _ _⟩
        rw [hM, map_sub, map_smul, ← hvw]
        convert hv using 1
        funext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
        simp [k, f]
      · refine sup_le (hMmono (Fin.castSucc_le_succ _)) ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hxb
    · intro g
      rw [hM, map_sub, hπmul]
      convert hchi g using 2
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, hπ, map_mul, hψk]
end GlobalTheory
