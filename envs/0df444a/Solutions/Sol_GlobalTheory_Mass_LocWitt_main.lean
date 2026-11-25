-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:20:05.513662+00:00
-- url     : https://prove2.me/submissions/562d7759-b8a1-4f7f-b511-4d76a8763967

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Theorems.Thm_GlobalTheory_Mass_LocWitt_abs_main
import Theorems.Thm_GlobalTheory_Mass_LocWitt_star_int
import Theorems.Thm_GlobalTheory_Mass_LocWitt_mem_hcompl

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
namespace GlobalTheory.Mass.LocWitt
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P = P → IsUnimodularAt h P L → ∀ x ∈ loc (K := K) P L, ∀ y ∈ loc (K := K) P L, h x x = h y y → (∃ w ∈ loc (K := K) P L, h w x = 1) → (∃ w ∈ loc (K := K) P L, h w y = 1) → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L ∧ g x = y := by
  intro K V _ _ _ _ _ _ _ _ h hK hs _ L _ P hP hc hu x hx y hy hn px py
  have hp := hP.isPrime
  have inj : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  have one : (1 : 𝓞 K) ∉ P := fun a => hP.ne_top ((Ideal.eq_top_iff_one P).2 a)
  have nm : ∀ {a b : 𝓞 K}, a ∉ P → b ∉ P → a * b ∉ P := fun ha hb e => (hp.mem_or_mem e).elim ha hb
  have mL : ∀ v, v ∈ loc (K := K) P L ↔ ∃ s, s ∉ P ∧ s • v ∈ L := fun v =>
    exists_congr fun s => and_congr_left' (mem_hcompl hP hc s)
  have mR : ∀ a : K, a ∈ locR (K := K) P ↔ ∃ s, s ∉ P ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a := fun a =>
    exists_congr fun s => and_congr (mem_hcompl hP hc s) (by rw [Submodule.mem_one, Algebra.smul_def])
  let A : Subring K :=
    { carrier := {a | a ∈ locR (K := K) P}
      zero_mem' := (locR (K := K) P).zero_mem
      add_mem' := fun ha hb => (locR (K := K) P).add_mem ha hb
      neg_mem' := fun ha => (locR (K := K) P).neg_mem ha
      one_mem' := (mR 1).2 ⟨1, one, 1, by simp⟩
      mul_mem' := by
        intro a b ha hb
        obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
        obtain ⟨s', hs', r', e'⟩ := (mR b).1 hb
        exact (mR _).2 ⟨s * s', nm hs hs', r * r', by rw [map_mul, map_mul, e, e']; ring⟩ }
  have mA : ∀ a, a ∈ A ↔ a ∈ locR (K := K) P := fun _ => Iff.rfl
  let M : AddSubgroup K :=
    { carrier := {a | ∃ s, s ∉ P ∧ ∃ r ∈ P, algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a}
      zero_mem' := ⟨1, one, 0, P.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨s, hs, r, hr, e⟩ ⟨s', hs', r', hr', e'⟩
        exact ⟨s * s', nm hs hs', s' * r + s * r', P.add_mem (P.mul_mem_left _ hr) (P.mul_mem_left _ hr'),
          by simp only [map_add, map_mul, e, e']; ring⟩
      neg_mem' := by
        rintro a ⟨s, hs, r, hr, e⟩
        exact ⟨s, hs, -r, P.neg_mem hr, by rw [map_neg, e]; ring⟩ }
  obtain ⟨θ, t, et, hθ⟩ := hK.2.2 P hP
  have key : Rel h (loc (K := K) P L).toAddSubgroup x y := by
    refine abs_main (A := A) (M := M) (θ := algebraMap (𝓞 K) K θ) hs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy hn px py
    · intro a ha
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      obtain ⟨s', es⟩ := star_int s
      obtain ⟨r', er⟩ := star_int r
      refine (mR _).2 ⟨s', fun a => hs ?_, r', by rw [er, es, e, star_mul']⟩
      rw [← hc]
      exact Ideal.subset_span ⟨s', a, by rw [es, star_star]⟩
    · intro a ha v hv
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      obtain ⟨s', hs', e'⟩ := (mL v).1 hv
      refine (mL _).2 ⟨s * s', nm hs hs', ?_⟩
      have : (s * s') • a • v = r • s' • v := by
        rw [← algebraMap_smul K (s * s'), ← algebraMap_smul K r, ← algebraMap_smul K s', smul_smul,
          smul_smul, e, map_mul]
        congr 1; ring
      rw [this]
      exact L.smul_mem r e'
    · intro v hv w hw
      have hw' : w ∈ dualAt h P (loc (K := K) P L) := by rw [hu]; exact hw
      simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap] at hw'
      exact hw' v hv
    · rintro a ha m ⟨s', hs', r', hr', e'⟩
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      exact ⟨s * s', nm hs hs', r * r', P.mul_mem_left _ hr', by rw [map_mul, map_mul, e, e']; ring⟩
    · rintro ⟨s, hs, r, hr, e⟩
      rw [mul_one] at e
      exact hs (inj e ▸ hr)
    · intro a ha haM
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      have hr : r ∉ P := fun hr => haM ⟨s, hs, r, hr, e⟩
      have a0 : a ≠ 0 := fun e0 => haM (e0 ▸ M.zero_mem)
      exact (mR _).2 ⟨r, hr, s, by rw [e]; field_simp⟩
    · exact (mR _).2 ⟨1, one, θ, by simp⟩
    · rintro ⟨s, hs, r, hr, e⟩
      rw [← et, ← map_sub, ← map_mul] at e
      exact nm hs hθ (inj e ▸ hr)
  obtain ⟨g, g1, g2, g3⟩ := key
  refine ⟨g, g1, ?_, g3⟩
  ext v
  simp only [gmap, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (g2 w).2 hw
  · intro hv
    refine ⟨g.symm v, (g2 _).1 (by simpa using hv), by simp⟩
end GlobalTheory.Mass.LocWitt
