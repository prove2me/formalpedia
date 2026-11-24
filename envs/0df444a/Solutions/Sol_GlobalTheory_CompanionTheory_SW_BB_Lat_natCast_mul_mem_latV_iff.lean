-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:04.441064+00:00
-- url     : https://prove2.me/submissions/fa00434a-5455-4da2-81ec-b5fb90a9f93d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteAdelicLatticeMembershipIff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_Lat_repr_map_evalV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_Lat_repr_natCast_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.Lat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.Lat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E),
    (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔
      ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ d M b a X
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (p : Fin 1) (i : Fin M) (k : Fin d),
      (Algebra.TensorProduct.basis (Fv F v) b).repr ((a : Fv F v ⊗[F] E) * projV v X p i) k =
        ((a : Af F) * cv (Af F) b (X 0) (i, k)) v := by
    intro v p i k
    obtain rfl : p = 0 := Subsingleton.elim _ _
    rw [repr_natCast_mul]
    have h := repr_map_evalV b v (X 0 i) k
    simp only [projV, h, cv]
    have h2 : ((a : Af F) * (Algebra.TensorProduct.basis (Af F) b).repr (X 0 i) k) v =
        evalV F v ((a : Af F) * (Algebra.TensorProduct.basis (Af F) b).repr (X 0 i) k) := rfl
    rw [h2, map_mul, map_natCast]
  constructor
  · rintro h ⟨i, k⟩ v
    rw [← key v 0 i k]
    exact h v 0 i k
  · intro h v p i k
    change (Algebra.TensorProduct.basis (Fv F v) b).repr ((a : Fv F v ⊗[F] E) * projV v X p i) k ∈ _
    rw [key v p i k]
    exact h (i, k) v
end GlobalTheory.CompanionTheory.SW.BB.Lat
