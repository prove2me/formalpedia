-- Prove2me | solution 1 for Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ac55bd8b-4b22-5035-bf08-a930aa041a18

import Mathlib
import Theorems.Thm_Module_Flat_ker_of_surjective_of_flat
import Theorems.Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range

set_option autoImplicit false

universe u

open TensorProduct

namespace CoreNak17

theorem subsingleton_of_forall_isMaximal {R : Type u} [CommRing R] {H : Type u} [AddCommGroup H] [Module R H]
    [Module.Finite R H] (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Subsingleton ((R ⧸ 𝔪) ⊗[R] H)) :
    Subsingleton H := by
  by_contra hne
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hne
  have hann : Module.annihilator R H ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ Module.annihilator R H := htop ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    obtain ⟨x, y, hxy⟩ := exists_pair_ne H
    exact hxy (by rw [← one_smul R x, ← one_smul R y, h1, h1])
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  have htop : (⊤ : Submodule R H) ≤ 𝔪 • ⊤ := by
    intro x _
    haveI : Subsingleton (H ⧸ (𝔪 • (⊤ : Submodule R H))) :=
      (TensorProduct.quotTensorEquivQuotSMul H 𝔪).symm.toEquiv.subsingleton
    rw [← Submodule.Quotient.mk_eq_zero]
    exact Subsingleton.elim _ _
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule R H) Module.Finite.fg_top htop
  have hr' : r ∈ Module.annihilator R H := Module.mem_annihilator.2 fun m => hr m Submodule.mem_top
  have h1 : (1 : R) ∈ 𝔪 := by
    have := 𝔪.sub_mem (hle hr') hr1
    rwa [sub_sub_cancel] at this
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem surjective_of_forall_isMaximal {R : Type u} [CommRing R] {M Z : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup Z] [Module R Z] (δ : M →ₗ[R] Z) [Module.Finite R (Z ⧸ LinearMap.range δ)]
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Surjective (δ.baseChange (R ⧸ 𝔪))) :
    Function.Surjective δ := by
  have hq : Subsingleton (Z ⧸ LinearMap.range δ) := by
    apply subsingleton_of_forall_isMaximal (R := R)
    intro 𝔪 _
    have hex := lTensor_exact (R ⧸ 𝔪) (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)
    have hs : Function.Surjective (LinearMap.lTensor (R ⧸ 𝔪) δ) := by
      have := h 𝔪
      rwa [LinearMap.baseChange_eq_ltensor] at this
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := LinearMap.lTensor_surjective (R ⧸ 𝔪) (Submodule.mkQ_surjective (LinearMap.range δ)) a
    obtain ⟨b', rfl⟩ := LinearMap.lTensor_surjective (R ⧸ 𝔪) (Submodule.mkQ_surjective (LinearMap.range δ)) b
    rw [(hex a').2 (hs a'), (hex b').2 (hs b')]
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  intro z
  rw [← Submodule.Quotient.mk_eq_zero]
  exact Subsingleton.elim _ _

section Trunc

variable {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (j : ℕ)

def T : ℕ → Type u
  | 0 => ↥(LinearMap.ker (d (j + 1)))
  | i + 1 => C (j + 1 + i)

scoped instance instTacg : ∀ i, AddCommGroup (T C d j i)
  | 0 => inferInstanceAs (AddCommGroup ↥(LinearMap.ker (d (j + 1))))
  | i + 1 => inferInstanceAs (AddCommGroup (C (j + 1 + i)))

scoped instance instTmod : ∀ i, Module R (T C d j i)
  | 0 => inferInstanceAs (Module R ↥(LinearMap.ker (d (j + 1))))
  | i + 1 => inferInstanceAs (Module R (C (j + 1 + i)))

def dT : ∀ i, T C d j i →ₗ[R] T C d j (i + 1)
  | 0 => (LinearMap.ker (d (j + 1))).subtype
  | i + 1 => d (j + 1 + i)

theorem flatT [∀ i, Module.Flat R (C i)] (hZ : Module.Flat R ↥(LinearMap.ker (d (j + 1)))) :
    ∀ i, Module.Flat R (T C d j i)
  | 0 => hZ
  | i + 1 => inferInstanceAs (Module.Flat R (C (j + 1 + i)))

end Trunc

theorem subtype_baseChange {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i)) (j : ℕ)
    (hZ : Module.Flat R ↥(LinearMap.ker (d (j + 1))))
    (hex : ∀ i, j + 1 ≤ i → LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective ((LinearMap.ker (d (j + 1))).subtype.baseChange A) ∧
      LinearMap.ker ((d (j + 1)).baseChange A) ≤ LinearMap.range ((LinearMap.ker (d (j + 1))).subtype.baseChange A) := by
  haveI := flatT C d j hZ
  have hdd' : ∀ i, dT C d j (i + 1) ∘ₗ dT C d j i = 0 := by
    intro i
    cases i with
    | zero =>
      ext ⟨x, hx⟩
      exact hx
    | succ i => exact hdd (j + 1 + i)
  have hbd' : ∀ i, n + 1 ≤ i → Subsingleton (T C d j i) := by
    intro i hi
    cases i with
    | zero => omega
    | succ i => exact hbd (j + 1 + i) (by omega)
  have h0 : LinearMap.ker (dT C d j 0) = ⊥ := Submodule.ker_subtype _
  have hex' : ∀ i, LinearMap.ker (dT C d j (i + 1)) ≤ LinearMap.range (dT C d j i) := by
    intro i
    cases i with
    | zero =>
      show LinearMap.ker (d (j + 1)) ≤ LinearMap.range (LinearMap.ker (d (j + 1))).subtype
      rw [Submodule.range_subtype]
    | succ i => exact hex (j + 1 + i) (by omega)
  obtain ⟨h1, h2⟩ := Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact (T C d j) (dT C d j) hdd' (n + 1)
    hbd' h0 hex' A
  exact ⟨LinearMap.ker_eq_bot.1 h1, h2 0⟩

end CoreNak17
p2m_reactivate "P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17"

open CoreNak17 in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange (R ⧸ 𝔪)) ≤ LinearMap.range ((d i).baseChange (R ⧸ 𝔪))) :
    ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by

  have key : ∀ k j : ℕ, j + k = n →
      Module.Flat R ↥(LinearMap.ker (d j)) ∧ ∀ i, j ≤ i → LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      haveI : ∀ i, n ≤ i → ∀ (x y : C i), x = y := fun i hi x y => (hbd i hi).elim x y
      refine ⟨?_, fun i hi x _ => ⟨0, ?_⟩⟩
      · haveI : Subsingleton ↥(LinearMap.ker (d j)) := ⟨fun x y => Subtype.ext (this j (by omega) _ _)⟩
        exact Module.Flat.of_free
      · exact this (i + 1) (by omega) _ _
    | succ k ih =>
      intro j hj
      obtain ⟨hZ, hexj⟩ := ih (j + 1) (by omega)

      have hmem : ∀ c, d j c ∈ LinearMap.ker (d (j + 1)) := fun c => by
        rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]
      let δ : C j →ₗ[R] ↥(LinearMap.ker (d (j + 1))) := (d j).codRestrict _ hmem
      haveI : Module.Finite R (↥(LinearMap.ker (d (j + 1))) ⧸ LinearMap.range δ) := by
        rw [LinearMap.range_codRestrict]; exact hfin j

      have hδK : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Surjective (δ.baseChange (R ⧸ 𝔪)) := by
        intro 𝔪 _
        obtain ⟨hinj, -⟩ := subtype_baseChange C d hdd n hbd j hZ hexj (R ⧸ 𝔪)
        intro z
        have hz : (LinearMap.ker (d (j + 1))).subtype.baseChange (R ⧸ 𝔪) z ∈ LinearMap.ker ((d (j + 1)).baseChange (R ⧸ 𝔪)) := by
          rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
          have : d (j + 1) ∘ₗ (LinearMap.ker (d (j + 1))).subtype = 0 := by
            ext ⟨y, hy⟩; exact hy
          rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]
        obtain ⟨c, hc⟩ := hfib 𝔪 j hz
        refine ⟨c, hinj ?_⟩
        rw [← hc, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
        simp only [δ, LinearMap.subtype_comp_codRestrict]
      have hδ : Function.Surjective δ := surjective_of_forall_isMaximal δ hδK
      refine ⟨?_, fun i hi => ?_⟩
      · have hflat := Module.Flat.ker_of_surjective_of_flat δ hδ
        rwa [LinearMap.ker_codRestrict] at hflat
      · rcases Nat.eq_or_lt_of_le hi with h | h
        · subst h
          intro x hx
          obtain ⟨c, hc⟩ := hδ ⟨x, hx⟩
          exact ⟨c, congrArg Subtype.val hc⟩
        · exact hexj i (by omega)
  intro i
  exact (key n 0 (by omega)).2 i (Nat.zero_le i)

end S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
end P2MW
export P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range (solution)
