-- Prove2me | solution 1 for GlobalTheory.MassOrth.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:28:41.9009+00:00
-- url     : https://prove2.me/submissions/789d6afb-94e3-45ed-a6c8-a91519d1ba11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_exists_orth_gens
import Theorems.Thm_GlobalTheory_MassOrth_int_mem_biInt
import Theorems.Thm_GlobalTheory_MassOrth_mem_loc_span_iff
import Theorems.Thm_GlobalTheory_MassOrth_mem_locR_iff

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
namespace GlobalTheory.MassOrth
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, (∀ i l, i ≠ l → h (b i) (b l) = 0) ∧ ∀ x, x ∈ loc (K := K) P M ↔ ∀ i, b.repr x i ∈ locR (K := K) P := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd M hM P hP
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  obtain ⟨S, hS⟩ := hM.fg
  have hsp := hM.span_eq_top
  let Λ : Submodule (biInt (w.valuation K)) V := Submodule.span _ (S : Set V)
  have hΛ : ∀ x, x ∈ loc (K := K) P M ↔ x ∈ Λ := fun x => by
    rw [← hS]; exact mem_loc_span_iff w _ x
  have htop : Submodule.span K (Λ : Set V) = ⊤ := by
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_mono fun x hx => (hΛ x).1 ⟨1, Submonoid.one_mem _, by simpa using hx⟩
  obtain ⟨m, e, he1, he2, he3⟩ := exists_orth_gens (w.valuation K) h hs (algebraMap (𝓞 K) K θ)
    (int_mem_biInt w θ) (by
      rw [← ht, ← map_sub]; exact w.valuation_eq_one_iff_notMem.2 hθ) _ Λ
    (Submodule.fg_span S.finite_toSet) rfl (by
      intro x _ hx
      refine hnd.1 x fun y => ?_
      have h1 : Submodule.span K (Λ : Set V) ≤ LinearMap.ker (h x) :=
        Submodule.span_le.2 fun y hy => hx y hy
      exact h1 (htop ▸ Submodule.mem_top))
  have hli : LinearIndependent K e := LinearMap.linearIndependent_of_isOrthoᵢ (B := h)
    (fun i l hil => he1 i l hil) he2
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← htop, ← he3, Submodule.span_span_of_tower]
  let b0 := Module.Basis.mk hli hspan
  have hm : m = Module.finrank K V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  subst hm
  have hb : ⇑b0 = e := Module.Basis.coe_mk hli hspan
  refine ⟨b0, by rw [hb]; exact he1, fun x => ?_⟩
  rw [hΛ, ← he3, ← hb, Module.Basis.mem_span_iff_repr_mem]
  refine forall_congr' fun i => ?_
  rw [show locR (K := K) P = locR (K := K) w.asIdeal from rfl, mem_locR_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]; exact a.2
  · intro hk
    exact ⟨⟨_, hk⟩, rfl⟩
end GlobalTheory.MassOrth
