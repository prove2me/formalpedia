-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.midpoint_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:37.869379+00:00
-- url     : https://prove2.me/submissions/6e25d220-4299-4505-952b-d38294977ce8

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]


@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median


attribute [local simp] Lo Hi Mid Tmp Work Ruler Rem





lemma midpoint_exec (I : List Sym) (s : IState NS) (lo hi : ℕ)
    (lt ht rt : List Item) (hl : s.G Lo=.int (lo : ℤ)::lt)
    (hh : s.G Hi=.int (hi : ℤ)::ht) (hr : s.G Ruler=.int 2::rt) :
    IExec I Fin.elim0 midpoint s
      (s.upd Mid (.int (((lo+hi)/2 : ℕ) : ℤ)::s.G Mid)) (midpointCost lo hi) := by
  let s1 := s.upd Tmp (.int (lo : ℤ)::s.G Tmp)
  let s2 := s1.upd Work (.int (hi : ℤ)::s.G Work)
  let sa := (s2.upd Tmp (s.G Tmp)).upd Work (s.G Work)
  let s3 := sa.upd Mid (.int ((lo+hi : ℕ) : ℤ)::s.G Mid)
  let s4 := (s3.upd Mid (.int (((lo+hi)/2 : ℕ) : ℤ)::s.G Mid)).upd Rem
    (.int (((lo+hi)%2 : ℕ) : ℤ)::s.G Rem)
  let s5 := s4.upd Rem (s.G Rem)
  have h1 : IExec I Fin.elim0 (.op (.dup Lo Tmp)) s s1 (dupCost (zsz (lo : ℤ))+17) :=
    .op (IOp.Step.dup (L := lt) (by decide) hl)
  have h2 : IExec I Fin.elim0 (.op (.dup Hi Work)) s1 s2 (dupCost (zsz (hi : ℤ))+17) := by
    have he : s1.G Work=s.G Work := by simp [s1]
    simpa [s2,he] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.dup (s := s1) (i := Hi) (j := Work) (a := (hi : ℤ)) (L := ht)
          (by decide) (by simp [s1,hh])))
  have h3 : IExec I Fin.elim0 (.op (.add Tmp Work Mid)) s2 s3
      (addIntCost (zsz (lo : ℤ)+zsz (hi : ℤ))) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s2) (i := Tmp) (j := Work) (k := Mid)
        (a := (lo : ℤ)) (b := (hi : ℤ)) (Li := s.G Tmp) (Lj := s.G Work)
        (by decide) (by simp [s2,s1]) (by simp [s2]))
    simpa [s3,sa,s2,s1,Nat.cast_add] using h
  have h4 : IExec I Fin.elim0 (.op (.split Mid Ruler Rem)) s3 s4 321 := by
    have h : IExec I Fin.elim0 (.op (.split Mid Ruler Rem)) s3 _ (splitCost 1+17) :=
      .op (.split (m := 1) (a := ((lo+hi : ℕ) : ℤ)) (Li := s.G Mid) (Lj := rt) (by decide) (by decide) (by decide) (by simp [s3])
        (by simpa [s3,sa,s2,s1] using hr))
    have hq : sg ((lo+hi : ℕ) : ℤ) ((((lo+hi : ℕ) : ℤ)).natAbs/2)=(((lo+hi)/2 : ℕ) : ℤ) := by
      rw [sg,if_neg (not_lt_of_ge (Int.natCast_nonneg (lo+hi)))]
      simp only [Int.natAbs_natCast]
    have hm : sg ((lo+hi : ℕ) : ℤ) ((((lo+hi : ℕ) : ℤ)).natAbs%2)=(((lo+hi)%2 : ℕ) : ℤ) := by
      rw [sg,if_neg (not_lt_of_ge (Int.natCast_nonneg (lo+hi)))]
      simp only [Int.natAbs_natCast]
    simpa only [show (2 : ℕ)^1=2 from by norm_num,hq,hm,s4,
      show splitCost 1+17=321 from by norm_num [splitCost,moveCost,takeCost],
      s3,sa,s2,s1,upd_G_self,upd_G_ne _ (show Rem≠Mid by decide),
      upd_G_ne _ (show Rem≠Tmp by decide),upd_G_ne _ (show Rem≠Work by decide)] using h
  have h5 : IExec I Fin.elim0 (.op (.drop Rem)) s4 s5
      (2*zsz (((lo+hi)%2 : ℕ) : ℤ)+2) := .op (.drop (by simp [s4]))
  have he : s5=s.upd Mid (.int (((lo+hi)/2 : ℕ) : ℤ)::s.G Mid) := by
    apply itemState_ext
    · intro i
      by_cases hM : i=Mid
      · subst i; simp [s5,s4,s3,sa,s2,s1]
      by_cases hT : i=Tmp
      · subst i; simp [s5,s4,s3,sa,s2,s1]
      by_cases hW : i=Work
      · subst i; simp [s5,s4,s3,sa,s2,s1]
      by_cases hR : i=Rem
      · subst i; simp [s5,s4,s3,sa,s2,s1]
      simp [s5,s4,s3,sa,s2,s1,IState.upd,Function.update_apply,hM,hT,hW,hR]
    · rfl
    · rfl
  have h := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 h5)))
  rw [he] at h
  change IExec I Fin.elim0 midpoint s _ _ at h
  convert h using 1 <;> simp only [midpointCost] <;> omega



end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (lo hi : Nat)
  (lt ht rt : List.{0} NLogN.Item)
  (hl :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt lo)) lt))
  (hh :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt hi)) ht))
  (hr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))) rt)),
  @NLogN.IExec KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.midpoint s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) lo hi)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)))
    (KoanaKPaths.Machine.Median.midpointCost lo hi) := by
  exact @KoanaKPaths.Machine.Median.midpoint_exec
