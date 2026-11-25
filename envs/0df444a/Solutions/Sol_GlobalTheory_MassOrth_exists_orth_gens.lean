-- Prove2me | solution 1 for GlobalTheory.MassOrth.exists_orth_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:38.439941+00:00
-- url     : https://prove2.me/submissions/1c12e095-8e7c-472e-ac2a-a5543a0a25c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_exists_max_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
namespace GlobalTheory.MassOrth
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (θ : K)
    (hθ : θ ∈ biInt v) (hθ' : v (θ - star θ) = 1) (n : ℕ) :
    ∀ (Λ : Submodule (biInt v) V), Λ.FG → Module.finrank K (Submodule.span K (Λ : Set V)) = n →
      (∀ x ∈ Λ, (∀ y ∈ Λ, h x y = 0) → x = 0) →
      ∃ (m : ℕ) (e : Fin m → V), (∀ i l, i ≠ l → h (e i) (e l) = 0) ∧ (∀ i, h (e i) (e i) ≠ 0) ∧
        Submodule.span (biInt v) (Set.range e) = Λ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Λ hfg hn hnd
  obtain ⟨x, hx, hmax⟩ := exists_max_vector v h hs θ hθ hθ' Λ hfg
  by_cases h0 : h x x = 0
  · refine ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    symm
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff]
    intro y hy
    refine hnd y hy fun z hz => ?_
    have := hmax y hy z hz
    rw [h0, map_zero] at this
    exact v.zero_iff.1 (le_antisymm this zero_le)
  have hv0 : 0 < v (h x x) := zero_lt_iff.2 (v.ne_zero_iff.2 h0)
  have hxx : star (h x x) = h x x := hs.eq x x
  have hc : ∀ y ∈ Λ, h x y / h x x ∈ biInt v := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [map_div₀, div_le_one₀ hv0]; exact hmax x hx y hy
    · have : star (h x y) = h y x := hs.eq x y
      rw [star_div₀, hxx, this, map_div₀, div_le_one₀ hv0]; exact hmax y hy x hx
  let p : V →ₗ[K] V := LinearMap.id - (LinearMap.toSpanSingleton K V x).comp ((h x x)⁻¹ • h x)
  have hp : ∀ y, p y = y - (h x y / h x x) • x := by
    intro y; simp [p, div_eq_inv_mul]
  have hxp : ∀ y, h x (p y) = 0 := by
    intro y; rw [hp, map_sub, map_smul, smul_eq_mul]; field_simp; ring
  have hcx : ∀ y ∈ Λ, (h x y / h x x) • x ∈ Λ := fun y hy =>
    Λ.smul_mem (⟨_, hc y hy⟩ : biInt v) hx
  let Λ' : Submodule (biInt v) V := Λ.map (p.restrictScalars (biInt v))
  have hle : Λ' ≤ Λ := by
    rintro _ ⟨y, hy, rfl⟩
    change p y ∈ Λ
    rw [hp]; exact Λ.sub_mem hy (hcx y hy)
  have horth : ∀ y ∈ Λ', h x y = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hxp y
  have horth' : ∀ y ∈ Λ', h y x = 0 := by
    intro y hy
    have : star (h x y) = h y x := hs.eq x y
    rw [← this, horth y hy, star_zero]
  have hlt : Submodule.span K (Λ' : Set V) < Submodule.span K (Λ : Set V) := by
    refine lt_of_le_of_ne (Submodule.span_mono hle) fun heq => h0 ?_
    have h1 : Submodule.span K (Λ' : Set V) ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun y hy => horth y hy
    exact h1 (heq ▸ Submodule.subset_span hx)
  obtain ⟨m, e, he1, he2, he3⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Λ'
    (hfg.map _) rfl (by
      intro y hy hyz
      refine hnd y (hle hy) fun z hz => ?_
      have h1 := hyz (p z) ⟨z, hz, rfl⟩
      rw [hp, map_sub, map_smul, horth' y hy] at h1
      simpa using h1)
  have hem : ∀ i, e i ∈ Λ' := fun i => he3 ▸ Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m + 1, Fin.cons x e, ?_, ?_, ?_⟩
  · intro i l hil
    induction i using Fin.cases with
    | zero =>
      induction l using Fin.cases with
      | zero => exact absurd rfl hil
      | succ l => simpa using horth _ (hem l)
    | succ i =>
      induction l using Fin.cases with
      | zero => simpa using horth' _ (hem i)
      | succ l => simpa using he1 i l fun hh => hil (by rw [hh])
  · intro i
    induction i using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using he2 i
  · rw [Fin.range_cons, Submodule.span_insert, he3]
    refine le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hx) hle) fun y hy => ?_
    have e1 : y = (h x y / h x x) • x + p y := by rw [hp]; abel
    rw [e1]
    refine Submodule.add_mem_sup ?_ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hc y hy⟩ : biInt v) (Submodule.mem_span_singleton_self x)
end GlobalTheory.MassOrth
