-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.finite_range_of_frob_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:51.548435+00:00
-- url     : https://prove2.me/submissions/60d13e0d-c496-490f-8fe1-36517ec1c615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
import Theorems.Thm_GlobalTheory_WeilDeligne_IsSmooth_finite_range
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_eq_zpow_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob h) ^ m = 1) : (Set.range ρ).Finite := by
  refine (Set.Finite.image2 (· * ·) (Set.finite_range fun j : Fin m => ρ (frob h) ^ (j : ℕ))
    hρ.finite_range).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (h := h) deg_frob σ
  have hker : frob h ^ m ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  set k := deg σ
  have hk : frob h ^ k = frob h ^ ((k % m).toNat) * (frob h ^ m) ^ (k / m) := by
    rw [← zpow_natCast (frob h) m, ← zpow_mul, ← zpow_natCast (frob h) ((k % m).toNat),
      ← zpow_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne')),
      add_comm, Int.mul_ediv_add_emod]
  have hlt : (k % m).toNat < m := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hm : (0 : ℤ) < m)
    omega
  refine ⟨ρ (frob h) ^ ((k % m).toNat), ⟨⟨_, hlt⟩, rfl⟩, ρ (ineIncl h τ), ⟨τ, rfl⟩, ?_⟩
  have h2 : ρ ((frob h ^ m) ^ (k / m)) = 1 := (ρ.ker.zpow_mem hker _)
  show _ = ρ σ
  rw [hτ, hk, map_mul, map_mul, h2, mul_one, map_pow]
end GlobalTheory.WeilDeligne
