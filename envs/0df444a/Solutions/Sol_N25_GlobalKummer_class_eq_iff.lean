-- Prove2me | solution 1 for N25.GlobalKummer.class_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:40.213765+00:00
-- url     : https://prove2.me/submissions/77af81e1-7239-434b-afe3-1847fb502772

import Definitions.Def_N25_GlobalKummer

noncomputable section

namespace N25.GlobalKummer

/-- Equality of the division classes is exactly rational divisibility of their difference. -/
theorem _root_.solution (hPhi : PhiFiveZero) (P R : ↥M) (Q S : J)
    (hQ : piEnd Q = (P : J)) (hS : piEnd S = (R : J)) :
    groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) =
      groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi R S hS) ↔
        P - R ∈ piM.range := by
  rw [groupCohomology.H1π_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    change ↥V at v
    have he : ∀ σ : Gal,
        σ • (Q - S) - (Q - S) = σ • (v : J) - (v : J) := by
      intro σ
      have h := congrArg (fun f : Gal → vRep hPhi => (show ↥V from f σ).val) hv
      change σ • (v : J) - (v : J) =
        (σ • Q - Q) - (σ • S - S) at h
      rw [smul_sub]
      abel_nf at h ⊢
      exact h.symm
    have hfix : Q - S - (v : J) ∈ M := by
      intro σ
      change σ • (Q - S - (v : J)) = Q - S - (v : J)
      rw [smul_sub]
      have h := he σ
      linear_combination (norm := abel_nf) h
    refine ⟨⟨Q - S - v, hfix⟩, ?_⟩
    apply Subtype.ext
    change piEnd (Q - S - (v : J)) = (P : J) - (R : J)
    rw [map_sub, map_sub, hQ, hS, show piEnd (v : J) = 0 from v.2, sub_zero]
  · rintro ⟨T, hT⟩
    have hT' : piEnd (T : J) = (P : J) - (R : J) := congrArg Subtype.val hT
    let v : ↥V := ⟨Q - S - T, by
      change piEnd (Q - S - (T : J)) = 0
      rw [map_sub, map_sub, hQ, hS, hT', sub_self]⟩
    refine ⟨v, ?_⟩
    funext σ
    apply Subtype.ext
    change σ • (Q - S - (T : J)) - (Q - S - (T : J)) =
      (σ • Q - Q) - (σ • S - S)
    rw [smul_sub, smul_sub, T.property σ]
    abel

end N25.GlobalKummer
