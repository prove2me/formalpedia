-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_center_products_64_to_127
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:19:29.698848+00:00
-- url     : https://prove2.me/submissions/a2a3dcaf-7746-444c-a746-832cc1d65f55

import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 150000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace ProductEvidence

private def seq (f : ℕ → ℤ) (n s : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | m+1 => f s+base*seq f m (s+1)

private theorem seq_eq (f : ℕ → ℤ) (n s : ℕ) :
    seq f n s=pack base (fun k => f (s+k)) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [seq,pack,ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem rowFrom (a : ℕ) (h : row a=seq (wc a) 252 0*seq (pc a) 252 0)
    (hb : (List.range 252).all (good a)=true) : rowHolds a := by
  refine ⟨?_,hb⟩
  simpa only [seq_eq,Nat.zero_add,rowProduct] using h
private theorem row64 : rowHolds 64 := rowFrom 64 (by decide +kernel) (by decide +kernel)
private theorem row65 : rowHolds 65 := rowFrom 65 (by decide +kernel) (by decide +kernel)
private theorem row66 : rowHolds 66 := rowFrom 66 (by decide +kernel) (by decide +kernel)
private theorem row67 : rowHolds 67 := rowFrom 67 (by decide +kernel) (by decide +kernel)
private theorem row68 : rowHolds 68 := rowFrom 68 (by decide +kernel) (by decide +kernel)
private theorem row69 : rowHolds 69 := rowFrom 69 (by decide +kernel) (by decide +kernel)
private theorem row70 : rowHolds 70 := rowFrom 70 (by decide +kernel) (by decide +kernel)
private theorem row71 : rowHolds 71 := rowFrom 71 (by decide +kernel) (by decide +kernel)
private theorem row72 : rowHolds 72 := rowFrom 72 (by decide +kernel) (by decide +kernel)
private theorem row73 : rowHolds 73 := rowFrom 73 (by decide +kernel) (by decide +kernel)
private theorem row74 : rowHolds 74 := rowFrom 74 (by decide +kernel) (by decide +kernel)
private theorem row75 : rowHolds 75 := rowFrom 75 (by decide +kernel) (by decide +kernel)
private theorem row76 : rowHolds 76 := rowFrom 76 (by decide +kernel) (by decide +kernel)
private theorem row77 : rowHolds 77 := rowFrom 77 (by decide +kernel) (by decide +kernel)
private theorem row78 : rowHolds 78 := rowFrom 78 (by decide +kernel) (by decide +kernel)
private theorem row79 : rowHolds 79 := rowFrom 79 (by decide +kernel) (by decide +kernel)
private theorem row80 : rowHolds 80 := rowFrom 80 (by decide +kernel) (by decide +kernel)
private theorem row81 : rowHolds 81 := rowFrom 81 (by decide +kernel) (by decide +kernel)
private theorem row82 : rowHolds 82 := rowFrom 82 (by decide +kernel) (by decide +kernel)
private theorem row83 : rowHolds 83 := rowFrom 83 (by decide +kernel) (by decide +kernel)
private theorem row84 : rowHolds 84 := rowFrom 84 (by decide +kernel) (by decide +kernel)
private theorem row85 : rowHolds 85 := rowFrom 85 (by decide +kernel) (by decide +kernel)
private theorem row86 : rowHolds 86 := rowFrom 86 (by decide +kernel) (by decide +kernel)
private theorem row87 : rowHolds 87 := rowFrom 87 (by decide +kernel) (by decide +kernel)
private theorem row88 : rowHolds 88 := rowFrom 88 (by decide +kernel) (by decide +kernel)
private theorem row89 : rowHolds 89 := rowFrom 89 (by decide +kernel) (by decide +kernel)
private theorem row90 : rowHolds 90 := rowFrom 90 (by decide +kernel) (by decide +kernel)
private theorem row91 : rowHolds 91 := rowFrom 91 (by decide +kernel) (by decide +kernel)
private theorem row92 : rowHolds 92 := rowFrom 92 (by decide +kernel) (by decide +kernel)
private theorem row93 : rowHolds 93 := rowFrom 93 (by decide +kernel) (by decide +kernel)
private theorem row94 : rowHolds 94 := rowFrom 94 (by decide +kernel) (by decide +kernel)
private theorem row95 : rowHolds 95 := rowFrom 95 (by decide +kernel) (by decide +kernel)
private theorem row96 : rowHolds 96 := rowFrom 96 (by decide +kernel) (by decide +kernel)
private theorem row97 : rowHolds 97 := rowFrom 97 (by decide +kernel) (by decide +kernel)
private theorem row98 : rowHolds 98 := rowFrom 98 (by decide +kernel) (by decide +kernel)
private theorem row99 : rowHolds 99 := rowFrom 99 (by decide +kernel) (by decide +kernel)
private theorem row100 : rowHolds 100 := rowFrom 100 (by decide +kernel) (by decide +kernel)
private theorem row101 : rowHolds 101 := rowFrom 101 (by decide +kernel) (by decide +kernel)
private theorem row102 : rowHolds 102 := rowFrom 102 (by decide +kernel) (by decide +kernel)
private theorem row103 : rowHolds 103 := rowFrom 103 (by decide +kernel) (by decide +kernel)
private theorem row104 : rowHolds 104 := rowFrom 104 (by decide +kernel) (by decide +kernel)
private theorem row105 : rowHolds 105 := rowFrom 105 (by decide +kernel) (by decide +kernel)
private theorem row106 : rowHolds 106 := rowFrom 106 (by decide +kernel) (by decide +kernel)
private theorem row107 : rowHolds 107 := rowFrom 107 (by decide +kernel) (by decide +kernel)
private theorem row108 : rowHolds 108 := rowFrom 108 (by decide +kernel) (by decide +kernel)
private theorem row109 : rowHolds 109 := rowFrom 109 (by decide +kernel) (by decide +kernel)
private theorem row110 : rowHolds 110 := rowFrom 110 (by decide +kernel) (by decide +kernel)
private theorem row111 : rowHolds 111 := rowFrom 111 (by decide +kernel) (by decide +kernel)
private theorem row112 : rowHolds 112 := rowFrom 112 (by decide +kernel) (by decide +kernel)
private theorem row113 : rowHolds 113 := rowFrom 113 (by decide +kernel) (by decide +kernel)
private theorem row114 : rowHolds 114 := rowFrom 114 (by decide +kernel) (by decide +kernel)
private theorem row115 : rowHolds 115 := rowFrom 115 (by decide +kernel) (by decide +kernel)
private theorem row116 : rowHolds 116 := rowFrom 116 (by decide +kernel) (by decide +kernel)
private theorem row117 : rowHolds 117 := rowFrom 117 (by decide +kernel) (by decide +kernel)
private theorem row118 : rowHolds 118 := rowFrom 118 (by decide +kernel) (by decide +kernel)
private theorem row119 : rowHolds 119 := rowFrom 119 (by decide +kernel) (by decide +kernel)
private theorem row120 : rowHolds 120 := rowFrom 120 (by decide +kernel) (by decide +kernel)
private theorem row121 : rowHolds 121 := rowFrom 121 (by decide +kernel) (by decide +kernel)
private theorem row122 : rowHolds 122 := rowFrom 122 (by decide +kernel) (by decide +kernel)
private theorem row123 : rowHolds 123 := rowFrom 123 (by decide +kernel) (by decide +kernel)
private theorem row124 : rowHolds 124 := rowFrom 124 (by decide +kernel) (by decide +kernel)
private theorem row125 : rowHolds 125 := rowFrom 125 (by decide +kernel) (by decide +kernel)
private theorem row126 : rowHolds 126 := rowFrom 126 (by decide +kernel) (by decide +kernel)
private theorem row127 : rowHolds 127 := rowFrom 127 (by decide +kernel) (by decide +kernel)

end ProductEvidence
open ProductEvidence in
theorem solution : ∀ a : ℕ, 64 ≤ a → a < 128 → rowHolds a := by
  intro a hl hu
  by_cases h96 : a < 96
  ·
    by_cases h80 : a < 80
    ·
      by_cases h72 : a < 72
      ·
        by_cases h68 : a < 68
        ·
          rcases (show a=64 ∨ a=65 ∨ a=66 ∨ a=67 by omega) with rfl|rfl|rfl|rfl
          · exact row64
          · exact row65
          · exact row66
          · exact row67
        ·
          rcases (show a=68 ∨ a=69 ∨ a=70 ∨ a=71 by omega) with rfl|rfl|rfl|rfl
          · exact row68
          · exact row69
          · exact row70
          · exact row71
      ·
        by_cases h76 : a < 76
        ·
          rcases (show a=72 ∨ a=73 ∨ a=74 ∨ a=75 by omega) with rfl|rfl|rfl|rfl
          · exact row72
          · exact row73
          · exact row74
          · exact row75
        ·
          rcases (show a=76 ∨ a=77 ∨ a=78 ∨ a=79 by omega) with rfl|rfl|rfl|rfl
          · exact row76
          · exact row77
          · exact row78
          · exact row79
    ·
      by_cases h88 : a < 88
      ·
        by_cases h84 : a < 84
        ·
          rcases (show a=80 ∨ a=81 ∨ a=82 ∨ a=83 by omega) with rfl|rfl|rfl|rfl
          · exact row80
          · exact row81
          · exact row82
          · exact row83
        ·
          rcases (show a=84 ∨ a=85 ∨ a=86 ∨ a=87 by omega) with rfl|rfl|rfl|rfl
          · exact row84
          · exact row85
          · exact row86
          · exact row87
      ·
        by_cases h92 : a < 92
        ·
          rcases (show a=88 ∨ a=89 ∨ a=90 ∨ a=91 by omega) with rfl|rfl|rfl|rfl
          · exact row88
          · exact row89
          · exact row90
          · exact row91
        ·
          rcases (show a=92 ∨ a=93 ∨ a=94 ∨ a=95 by omega) with rfl|rfl|rfl|rfl
          · exact row92
          · exact row93
          · exact row94
          · exact row95
  ·
    by_cases h112 : a < 112
    ·
      by_cases h104 : a < 104
      ·
        by_cases h100 : a < 100
        ·
          rcases (show a=96 ∨ a=97 ∨ a=98 ∨ a=99 by omega) with rfl|rfl|rfl|rfl
          · exact row96
          · exact row97
          · exact row98
          · exact row99
        ·
          rcases (show a=100 ∨ a=101 ∨ a=102 ∨ a=103 by omega) with rfl|rfl|rfl|rfl
          · exact row100
          · exact row101
          · exact row102
          · exact row103
      ·
        by_cases h108 : a < 108
        ·
          rcases (show a=104 ∨ a=105 ∨ a=106 ∨ a=107 by omega) with rfl|rfl|rfl|rfl
          · exact row104
          · exact row105
          · exact row106
          · exact row107
        ·
          rcases (show a=108 ∨ a=109 ∨ a=110 ∨ a=111 by omega) with rfl|rfl|rfl|rfl
          · exact row108
          · exact row109
          · exact row110
          · exact row111
    ·
      by_cases h120 : a < 120
      ·
        by_cases h116 : a < 116
        ·
          rcases (show a=112 ∨ a=113 ∨ a=114 ∨ a=115 by omega) with rfl|rfl|rfl|rfl
          · exact row112
          · exact row113
          · exact row114
          · exact row115
        ·
          rcases (show a=116 ∨ a=117 ∨ a=118 ∨ a=119 by omega) with rfl|rfl|rfl|rfl
          · exact row116
          · exact row117
          · exact row118
          · exact row119
      ·
        by_cases h124 : a < 124
        ·
          rcases (show a=120 ∨ a=121 ∨ a=122 ∨ a=123 by omega) with rfl|rfl|rfl|rfl
          · exact row120
          · exact row121
          · exact row122
          · exact row123
        ·
          rcases (show a=124 ∨ a=125 ∨ a=126 ∨ a=127 by omega) with rfl|rfl|rfl|rfl
          · exact row124
          · exact row125
          · exact row126
          · exact row127
