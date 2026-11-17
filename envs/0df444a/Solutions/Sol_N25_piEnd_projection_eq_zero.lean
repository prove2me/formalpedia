-- Prove2me | solution 1 for N25.piEnd_projection_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:08.902861+00:00
-- url     : https://prove2.me/submissions/dbbf0dea-6a02-4e87-828f-a16a24926f46

import Definitions.Def_N25_LocalKummerPolynomial

set_option autoImplicit false

namespace N25

/-- The integral polynomial projector onto the selected prime component sends
71-torsion into the kernel of the selected endomorphism. -/
theorem _root_.solution (hPhi : PhiFiveZero) (x : J)
    (hx : 71 • x = 0) :
    piEnd (3 • x + 18 • gamma x + 22 • gamma (gamma x) +
      42 • gamma (gamma (gamma x))) = 0 := by
  have h0 := hPhi x
  have h1 := hPhi (gamma x)
  have h2 := congrArg gamma (congrArg gamma hx)
  have h3 := congrArg gamma h2
  have h4 := congrArg gamma h3
  simp only [map_nsmul, map_zero] at h2 h3 h4
  simp only [piEnd, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.comp_apply, map_add, map_nsmul]
  have hs := congrArg₂ (fun u v : J => u + v)
    (congrArg₂ (fun u v : J => u + v)
      (congrArg₂ (fun u v : J => u + v)
        (congrArg₂ (fun u v : J => u + v)
          (congrArg (fun y : J => (6 : ℕ) • y) h0)
          (congrArg (fun y : J => (42 : ℕ) • y) h1)) h2)
      (congrArg (fun y : J => (2 : ℕ) • y) h3))
    (congrArg (fun y : J => (2 : ℕ) • y) h4)
  simp only [nsmul_zero, zero_add] at hs
  abel_nf at hs ⊢
  exact hs

end N25
