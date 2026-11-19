-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.nativeTrialCost_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.252342+00:00
-- url     : https://prove2.me/submissions/b1dbf680-174d-4da5-a968-3a8ba7221b37

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

lemma nativeTrialCost_polynomial (n k m : ℕ) (hk : 1≤ k) :
    nativeTrialCost n k m≤1000000000000000*2^k*(1+n+k+m)^10 := by
  let p := 1+n+k+m
  let e := 2^k
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hn : n ≤ p := by dsimp [p]; omega
  have hk' : k ≤ p := by dsimp [p]; omega
  have hm : m ≤ p := by dsimp [p]; omega
  have hd : k-1 ≤ p := by omega
  have hw : wordWidth n k ≤ 100*p^2 := by
    unfold wordWidth
    gcongr
    dsimp [p]; omega
  have ht : trialBits n k ≤ p*p+(p*p+p*(p*(p*p))) := by
    unfold trialBits
    gcongr
  let w := 100*p^2
  let t := p*p+(p*p+p*(p*(p*p)))
  let fc := 10000000*(w+p+2)^2*e+10000*(t+1)
  let fv := (500000*(w+1)^2+10000*(t+1)+fc+1000)*(p+1)+100000*(w+1)^2
  let fl := (fv+31)*p+1000*(w+1)*(p+1)+2000*(w+1)*e*(p*p+1)
  let pc := 1000000*(w+1)^2+10000*(w+1)*e*(p*p+1)+10000*(w+2)*(e+1)+10000*(t+1)
  let pv := (pc+56)*p+7000*(p+1)*(p+1)+15000*(w+1)^2+1000*(p+1)
  let lc := (pv+31)*p+2000000*(p+2)^2*(w+p+2)*e+20000*(w+1)^2+1000*(p+1)
  let lv := (500000*(w+1)^2+10000*(t+1)+lc+1000)*(p+1)+100000*(w+1)^2
  let ll := (lv+31)*p+1000*(w+1)*(p+1)+(2*w+57)*(e+1)*(p*p)+100+2000*(w+1)*e*(p*p+1)
  let ld := (ll+13000*(w+1)^2+31)*p+25000*(w+1)^2+1200*(p+1)
  let tc := 100000*(w+1)^2+10000*(w+1)*e*(p*p+1)+10000*(w+2)*(e+1)
  let ns := (tc+31)*p+50000*(w+1)^2*(e+1)+1000*(p+1)
  let nd := (ns+31)*p+3000*(w+1)*(p+1)
  let total := 180000*(w+1)^2+500*(t+1)+fl+ld+nd+(2*w+57)*(e+1)*(p*p)+100
  have hmajor : nativeTrialCost n k m ≤ total := by
    dsimp [total,fl,fv,fc,ld,ll,lv,lc,pv,pc,nd,ns,tc]
    unfold nativeTrialCost firstLayerCost firstVertexCost firstCellCost layerDriverCost laterLayerCost
      laterVertexCost laterCellCost predecessorVertexCost predecessorCellCost normDriverCost normStateCost terminalCellCost
    gcongr
  have he : 1 ≤ e := Nat.one_le_pow k 2 (by omega)
  change nativeTrialCost n k m ≤ 1000000000000000*e*p^10
  apply hmajor.trans
  dsimp [total,fl,fv,fc,ld,ll,lv,lc,pv,pc,nd,ns,tc,w,t]
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le he
  rw [hj,hr]
  ring_nf
  omega

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (n k m : Nat) (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
  @LE.le.{0} Nat instLENat (KoanaKPaths.Machine.Trial.nativeTrialCost n k m)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000000000000000) (instOfNatNat (nat_lit 1000000000000000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
            k)
          m)
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) := by
  exact @KoanaKPaths.Machine.Trial.nativeTrialCost_polynomial
