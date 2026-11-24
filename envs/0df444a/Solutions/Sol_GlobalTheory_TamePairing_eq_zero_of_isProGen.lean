-- Prove2me | solution 1 for GlobalTheory.TamePairing.eq_zero_of_isProGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:38.769313+00:00
-- url     : https://prove2.me/submissions/84736e7a-cf39-4876-b161-75954553cacf

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_GlobalTheory_TameQuot_mem_proKer
import Theorems.Thm_ReciprocityTheory_Gal_Ine_le_Dec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot
namespace GlobalTheory.TamePairing
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [hl : Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω} {γ₀ : Dec (F := F) A}
    (hγ : IsProGen F A l (γ₀ : G F Ω)) (f : Dec (F := F) A → ZMod (l ^ n)) (hf : Continuous f)
    (hadd : ∀ g h, f (g * h) = f g + f h) (h0 : f γ₀ = 0) (σ : Dec (F := F) A)
    (hσ : (σ : G F Ω) ∈ Ine (F := F) A) : f σ = 0 := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  let φ : Dec (F := F) A →* Multiplicative (ZMod (l ^ n)) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) (fun g h => by rw [hadd, ofAdd_add])
  let ψ : Ine (F := F) A →* Multiplicative (ZMod (l ^ n)) :=
    φ.comp (Subgroup.inclusion (Ine_le_Dec A))
  have hc : Continuous fun g : Ine (F := F) A => f (Subgroup.inclusion (Ine_le_Dec A) g) :=
    hf.comp (continuous_induced_rng.2 continuous_subtype_val)
  have hker : (ψ.ker : Set (Ine (F := F) A)) =
      (fun g : Ine (F := F) A => f (Subgroup.inclusion (Ine_le_Dec A) g)) ⁻¹' {0} := by
    ext g; rfl
  have hopen : IsOpen (ψ.ker : Set (Ine (F := F) A)) := by
    rw [hker]; exact (isOpen_discrete _).preimage hc
  have hclosed : IsClosed (ψ.ker : Set (Ine (F := F) A)) := by
    rw [hker]; exact (isClosed_discrete _).preimage hc
  have hidx : ∃ m : ℕ, ψ.ker.index = l ^ m := by
    have h1 : ψ.ker.index ∣ l ^ n := by
      rw [Subgroup.index_ker]
      have := Subgroup.card_subgroup_dvd_card ψ.range
      simpa using this
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl.out).1 h1
    exact ⟨m, hm⟩
  have hle : Subgroup.zpowers (γ₀ : G F Ω) ⊔ ineKer F A l ≤
      ψ.ker.map (Ine (F := F) A).subtype := by
    refine sup_le ?_ (Subgroup.map_mono fun x hx => mem_proKer.1 hx _ inferInstance hopen hidx)
    rw [Subgroup.zpowers_le]
    refine ⟨⟨γ₀, hγ.1⟩, ?_, rfl⟩
    rw [hker]; exact h0
  have h2 : (σ : G F Ω) ∈ closure ((↑) '' (ψ.ker : Set (Ine (F := F) A)) : Set (G F Ω)) :=
    closure_mono (s := ((Subgroup.zpowers (γ₀ : G F Ω) ⊔ ineKer F A l : Subgroup (G F Ω)) :
      Set (G F Ω))) hle (hγ.2 hσ)
  have h3 : (⟨σ, hσ⟩ : Ine (F := F) A) ∈ closure (ψ.ker : Set (Ine (F := F) A)) :=
    closure_subtype.2 h2
  rw [hclosed.closure_eq, hker] at h3
  exact h3
end GlobalTheory.TamePairing
