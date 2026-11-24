-- Prove2me | solution 1 for GlobalTheory.Published.StoneVonNeumann_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:40.989676+00:00
-- url     : https://prove2.me/submissions/b44e220c-d585-4274-8bf2-7d43e8611549

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp
import Theorems.Thm_GlobalTheory_Published_SvN_transl_indicator
import Theorems.Thm_GlobalTheory_Published_SvN_exists_data
import Theorems.Thm_GlobalTheory_Published_SvN_exists_eigen_mem
import Theorems.Thm_GlobalTheory_Published_SvN_exists_irr_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
namespace GlobalTheory.Published
theorem _root_.solution : StoneVonNeumann := by
  intro F _ _ _ _ h2 W _ _ _ _ _ B hB hn ψ hψ hψ1
  obtain ⟨A, α, hα, hA, k1, k2, k3⟩ := SvN.exists_data h2 hB hn hψ hψ1
  constructor
  · obtain ⟨P, -, hP⟩ := SvN.exists_irr_sub (π := SvN.funRep hB ψ) hB hα hA k1 k2 k3 hψ
      (fun t v => by simp [SvN.funRep, (SvN.ops_transl (SvN.alt_psi hB ψ)).zero]) (e := (A : Set W).indicator α)
      (fun h => hα.ne 0 A.zero_mem (by simpa using congrFun h 0))
      (fun a ha => by simpa [SvN.funRep] using SvN.transl_indicator hα a ha)
    exact ⟨_, _, _, _, hP⟩
  · intro S S' _ _ _ _ ρ ρ' hρ hρ'
    have i1 := hρ.2.1
    have i2 := hρ'.2.1
    obtain ⟨e, -, he0, he⟩ := SvN.exists_eigen_mem hB hα k1 k2 hρ.2.2 hρ.1 ⊤ top_ne_bot
    obtain ⟨e', -, he0', he'⟩ := SvN.exists_eigen_mem hB hα k1 k2 hρ'.2.2 hρ'.1 ⊤ top_ne_bot
    obtain ⟨P, heP, hP⟩ := SvN.exists_irr_sub (π := ρ.prod ρ') hB hα hA k1 k2 k3 hψ
      (fun t v => Prod.ext (hρ.2.2 t v.1) (hρ'.2.2 t v.2)) (e := (e, e'))
      (fun h => he0 (congrArg Prod.fst h)) (fun a ha => Prod.ext (he a ha) (he' a ha))
    have i3 := hP.2.1
    let f : P.toRepresentation.IntertwiningMap ρ :=
      ⟨(LinearMap.fst ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    let f' : P.toRepresentation.IntertwiningMap ρ' :=
      ⟨(LinearMap.snd ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    have hf := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right fun h =>
      he0 (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ => k ⟨_, heP⟩) h)
    have hf' := (Representation.IsIrreducible.bijective_or_eq_zero f').resolve_right fun h =>
      he0' (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ' => k ⟨_, heP⟩) h)
    exact ⟨(f.ofBijective hf).symm.trans (f'.ofBijective hf')⟩
end GlobalTheory.Published
