-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_finite_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:31.03167+00:00
-- url     : https://prove2.me/submissions/2e8cd514-bc9a-48c0-95fa-3aa878c84e03

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Theorems.Thm_GlobalTheory_HermClass_finite_between
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_representatives
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_orthogonal_lengths
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_residues
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral
import Theorems.Thm_GlobalTheory_HermClass_fg_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HermClass
theorem _root_.solution {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ x y, h y x = star (h x y))
    (hnd : ∀ y, (∀ x, h y x = 0) → y = 0) {N m : ℤ} (hN : N ≠ 0) (hm : m ≠ 0)
    {α : Type*} {ι : Type*} [Finite ι] (Λ : α → Submodule ℤ V) (t : α → ι → V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h (γ x) (γ y) = h x y) ∧
      (∀ x, x ∈ Λ a ↔ γ x ∈ Λ s) ∧ ∀ i, ∃ y ∈ Λ s, γ (t a i) - t s i = m • y := by
  classical
  set n := finrank E V with hn
  obtain ⟨S₀, hS₀f, hS₀0, hS₀⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  have hv : ∀ a, ∃ v : Fin n → V, (∀ i, v i ∈ Λ a) ∧
      (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S₀ := fun a =>
    hS₀ V h (Λ a) hn.symm hs hnd (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  choose v hvΛ hvo hvS using hv
  have hexp : ∀ a (c : Fin n → E) (y : V), h (∑ i, c i • v a i) y = ∑ i, c i * h (v a i) y := by
    intro a c y
    simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
  have hexp2 : ∀ a (x : V) (c : Fin n → E),
      h x (∑ j, c j • v a j) = ∑ j, star (c j) * h x (v a j) := by
    intro a x c
    simp [map_sum, smul_eq_mul, starRingEnd_apply]
  have hcoef : ∀ a (c : Fin n → E) j, h (∑ i, c i • v a i) (v a j) = c j * h (v a j) (v a j) := by
    intro a c j
    rw [hexp, Finset.sum_eq_single j]
    · intro i _ hij
      rw [hvo a i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hd0 : ∀ a j, h (v a j) (v a j) ≠ 0 := fun a j h0 => hS₀0 (h0 ▸ hvS a j)
  have hli : ∀ a, LinearIndependent E (v a) := by
    intro a
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := hcoef a c j
    rw [hc, map_zero, LinearMap.zero_apply] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hd0 a j)
  let b : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) ((Fintype.card_fin n).trans hn)
  let Φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (b a).equivFun
  have hΦsymm : ∀ a c, (Φ a).symm c = ∑ i, c i • v a i := by
    intro a c
    simp [Φ, b, Basis.equivFun_symm_apply]
  have hgram : ∀ a (c c' : Fin n → E), h (∑ i, c i • v a i) (∑ j, c' j • v a j) =
      ∑ i, c i * (star (c' i) * h (v a i) (v a i)) := by
    intro a c c'
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp2, Finset.sum_eq_single i]
    · intro j _ hji
      rw [hvo a i j (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  obtain ⟨M, hM0, hMT⟩ := exists_int_mul_isIntegral E (hS₀f.image fun d => d⁻¹)
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : ∀ c, c ∈ L₀ ↔ ∀ i, IsIntegral ℤ (c i) := by
    intro c
    simp [L₀, Submodule.mem_pi, mem_integralClosure_iff]
  have hL₀fg : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  let P : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((Φ a : V →ₗ[E] (Fin n → E)).restrictScalars ℤ)
  have hmemP : ∀ a c, c ∈ P a ↔ (Φ a).symm c ∈ Λ a := by
    intro a c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hc
      exact ⟨_, hc, by simp⟩
  have hPfg : ∀ a, (P a).FG := fun a => (hfg a).map _
  have hPB : ∀ a, P a ∈ {L : Submodule ℤ (Fin n → E) | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} := by
    intro a
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [hmemP, hΦsymm]
      exact Submodule.sum_mem _ fun i _ => hO a (c i) ((hL₀ c).1 hc i) _ (hvΛ a i)
    · rw [hL₀]
      intro i
      have hx := (hmemP a c).1 hc
      have hci := hcoef a c i
      rw [← hΦsymm] at hci
      have : (M : E) * c i = ((M : E) * (h (v a i) (v a i))⁻¹) * h ((Φ a).symm c) (v a i) := by
        rw [hci]
        field_simp [hd0 a i]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact (hMT _ ⟨_, hvS a i, rfl⟩).mul (hint a _ hx _ (hvΛ a i))
  have hB := finite_between (E := E) L₀ hL₀fg hM0
  have hres : ∀ Q : Submodule ℤ (Fin n → E), ∃ R : Set (Fin n → E), R.Finite ∧
      (Q.FG → ∀ x ∈ Q, ∃ ρ ∈ R, ∃ y ∈ Q, x = ρ + m • y) := by
    intro Q
    by_cases hQ : Q.FG
    · obtain ⟨R, hRf, -, hR⟩ := exists_finite_residues Q hQ hm
      exact ⟨R, hRf, fun _ => hR⟩
    · exact ⟨∅, Set.finite_empty, fun h' => absurd h' hQ⟩
  choose R hRf hR using hres
  have hρ : ∀ a i, ∃ ρ ∈ R (P a), ∃ y ∈ P a, Φ a (t a i) = ρ + m • y := fun a i =>
    hR (P a) (hPfg a) _ ((hmemP a _).2 (by simpa using ht a i))
  choose ρ hρR y hyP hρeq using hρ
  let f : α → (Fin n → E) × Submodule ℤ (Fin n → E) × (ι → Fin n → E) := fun a =>
    (fun i => h (v a i) (v a i), P a, ρ a)
  have hfin : (Set.range f).Finite := by
    refine ((Set.Finite.pi fun _ => hS₀f).prod (hB.prod
      (Set.Finite.pi fun _ => hB.biUnion fun Q _ => hRf Q))).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨fun i _ => hvS a i, hPB a, fun i _ => Set.mem_biUnion (hPB a) (hρR a i)⟩
  obtain ⟨S, hSf, hS⟩ := exists_finite_representatives f hfin
  refine ⟨S, hSf, fun a => ?_⟩
  obtain ⟨s, hsS, hfs⟩ := hS a
  simp only [f, Prod.mk.injEq] at hfs
  obtain ⟨hd, hP, hρ'⟩ := hfs
  refine ⟨s, hsS, (Φ a).trans (Φ s).symm, ?_, ?_, ?_⟩
  · intro x z
    obtain ⟨cx, rfl⟩ := (Φ a).symm.surjective x
    obtain ⟨cz, rfl⟩ := (Φ a).symm.surjective z
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    simp only [hΦsymm, hgram]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun hd i]
  · intro x
    have e1 := hmemP a (Φ a x)
    have e2 := hmemP s (Φ a x)
    rw [LinearEquiv.symm_apply_apply] at e1
    rw [hP] at e2
    simp only [LinearEquiv.trans_apply]
    exact e1.symm.trans e2
  · intro i
    refine ⟨(Φ s).symm (y a i - y s i), (hmemP s _).1 (sub_mem (by rw [hP]; exact hyP a i) (hyP s i)), ?_⟩
    apply (Φ s).injective
    simp only [LinearEquiv.trans_apply, map_sub, map_zsmul, LinearEquiv.apply_symm_apply]
    rw [hρeq a i, hρeq s i, congrFun hρ' i, smul_sub]
    abel
end GlobalTheory.HermClass
