-- Prove2me | solution 1 for GlobalTheory.GenusLatCompare.trivAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:39:06.583299+00:00
-- url     : https://prove2.me/submissions/44382271-5773-4d63-8d6d-bd903d098e1a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Theorems.Thm_GlobalTheory_GenusLatCompare_span_smul_le_iff
import Theorems.Thm_GlobalTheory_GenusLatCompare_exists_uniform
import Theorems.Thm_GlobalTheory_GenusLatCompare_eqAtPrime_of_trivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenusLatCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.GenusLatCompare
theorem _root_.solution (Λ : Lat E n) (s : ℕ) : (toGen Λ).TrivAt s ↔ Λ.StdAt s := by
  refine ⟨fun h p hp hs => eqAtPrime_of_trivAt _ h p hp hs, fun h => ?_⟩
  let J : Ideal ℤ :=
    { carrier := {k | (∀ x ∈ Λ.L, k • x ∈ stdMod E n) ∧ ∀ x ∈ stdMod E n, k • x ∈ Λ.L}
      add_mem' := fun {a b} ha hb =>
        ⟨fun x hx => by rw [add_smul]; exact add_mem (ha.1 x hx) (hb.1 x hx),
          fun x hx => by rw [add_smul]; exact add_mem (ha.2 x hx) (hb.2 x hx)⟩
      zero_mem' := ⟨fun x _ => by simp, fun x _ => by simp⟩
      smul_mem' := fun c a ha =>
        ⟨fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.1 x hx) c,
          fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.2 x hx) c⟩ }
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal J).principal
  have hdJ : ((d.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hd]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  refine ⟨d.natAbs, Nat.coprime_of_dvd fun p hp hpd hps => ?_, ?_, ?_⟩
  · obtain ⟨k₁, hk₁, h₁⟩ := exists_uniform hp Λ.fg (h p hp hps).1
    obtain ⟨k₂, hk₂, h₂⟩ := exists_uniform hp (Lat.std E n).fg (h p hp hps).2
    have hJ : ((k₁ * k₂ : ℕ) : ℤ) ∈ J :=
      ⟨fun x hx => by rw [natCast_zsmul, mul_comm, mul_smul]; exact nsmul_mem (h₁ x hx) _,
        fun x hx => by rw [natCast_zsmul, mul_smul]; exact nsmul_mem (h₂ x hx) _⟩
    rw [hd] at hJ
    have h3 : d.natAbs ∣ k₁ * k₂ := Int.natCast_dvd_natCast.1 (Int.natAbs_dvd.2 (Ideal.mem_span_singleton.1 hJ))
    exact (hp.dvd_mul.1 (hpd.trans h3)).elim hk₁ hk₂
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.1 x hx
    rwa [natCast_zsmul] at this
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.2 x hx
    rwa [natCast_zsmul] at this
end GlobalTheory.GenusLatCompare
