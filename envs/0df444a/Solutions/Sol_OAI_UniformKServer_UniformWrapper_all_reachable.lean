-- Prove2me | solution 1 for OAI.UniformKServer.UniformWrapper.all_reachable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:34.622663+00:00
-- url     : https://prove2.me/submissions/6d6e7d29-9bd2-4caa-af39-a2e9507b1db2

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008
import Theorems.Thm_OAI_UniformKServer_UniformWrapper_live_next

section
-- module Solutions.Q220_UK.UniformKServer_WrapperReachable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem live_initial {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (delay : ℕ) (hd : 2^c.2≤delay) (f : ℕ → CoreState mult)
    (z : MachineState (machine mult)) (hz : CoreRep (uniform mult) (f 0) z) :
    Live (n:=n) (k:=k) mult v c delay f 0 z := by
  left
  exact ⟨lt_of_lt_of_le (Nat.pow_pos (by decide)) hd,hz⟩

 theorem all_reachable_oai {n k : ℕ} (mult : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (d : RationalMetric n) (s : Configuration n k)
    (hb : CoreRep (uniform mult) a (boot (machine mult) 64 1 d s))
    (t : ℕ) (z : MachineState (machine mult)) (hz : Reachable (machine mult) 64 1 d s t z) :
    Live (n:=n) (k:=k) mult v c delay p.state t z := by
  induction hz with
  | boot=>
    apply live_initial mult v c delay hd p.state
    rw [p.start]
    exact hb
  | @next t z hz r coins ih=>
    exact (live_next mult (instanceCode d s).length hk hkn v hR hT c hc delay hd a p t z ih r coins).1

end UniformKServer.UniformWrapper

end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.UniformWrapper.all_reachable_oai := @OAI.UniformKServer.UniformWrapper.all_reachable_oai
